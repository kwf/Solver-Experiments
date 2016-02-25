{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}

module SimpleSolver where

import Control.Monad.State
import Control.Monad.Except
import Control.Arrow
import Data.List

import Text.Megaparsec hiding ( State, count )
import Text.Megaparsec.String
import Text.Megaparsec.Prim ( setPosition )
import Text.Megaparsec.Pos

import Language.Haskell.TH ( runIO, location, Loc(..) )
import Language.Haskell.TH.Quote
import Data.Data

import System.IO

-- Thoughts and musings so far...

-- NOTE: What about occurs check in work items (T3)? I don't have it here yet.

data Var = SrcVar String
         | FreshSkolem Integer
         | UnifVar Integer
           
data Type where
   TyConst :: Const -> Type
   TyVar :: Var -> Type
   TyApp :: Type -> Type -> Type
   TyFamApp :: (TyFam, Type) -> Type

newtype Const = Const String deriving ( Eq )
newtype TyFam = TyFam String deriving ( Eq )

-- data Flavor = G | W deriving ( Eq, Show )

-- data Flavored (f :: Flavor) a where
--    Given :: a -> Flavored G a
--    Wanted :: a -> Flavored W a

data Equality =
  Type :=: Type

data SolverError =
  Type :=/=: Type | TimeoutError

data Canonical where
   CanTyVar :: Var -> Type          -> Canonical
   CanTyFam :: (TyFam, Type) -> Var -> Canonical

uncanonicalize :: Canonical -> Equality
uncanonicalize (CanTyVar v t)   = TyVar v      :=: t
uncanonicalize (CanTyFam tfa v) = TyFamApp tfa :=: TyVar v

-- data SomeFlavor a =
--   forall f. SomeFlavor (Flavored f a)

type WorkList = [Equality]
type InertSet = [Canonical]
type SolverState = (Integer, WorkList, InertSet)
type History = [(Event, SolverState)]

-- Events which may appear in the solver log
data Event = SupplyFresh Integer
           | KickOutWith Canonical
           | AddInert Canonical
           | NextWorkItem Equality
           | AddToWorkList WorkList
           | Success
           | Finished
           deriving ( Eq, Show )

-- The solver monad is morally:
   -- exceptions of the type SolverError
   -- unique supply of numeric identifiers for fresh variables
   -- state of the inert set
   -- state of the work list
   -- log of all events so far
newtype Solver a =
  Solver { getSolver ::
              ExceptT SolverError
                (State (SolverState, History)) a }
  deriving (Functor, Applicative, Monad,
            MonadState (SolverState, History))

runSolver :: Solver a -> Either SolverError a
runSolver solver =
  fst $ runSolverLogging solver

runSolverLogging :: Solver a -> (Either SolverError a, History)
runSolverLogging solver =
    second (\(s, history) -> (Finished, s) : history)
  . flip runState ((0, [], []), [])
  . runExceptT
  . getSolver $ solver

update :: (SolverState -> (a, Event, SolverState)) -> Solver a
update f = do
  (s, history) <- get
  let (a, e, s') = f s
  put (s', (e, s') : history)
  return a

freshSkolem :: Solver Var
freshSkolem =
  update $ \(i, wl, is) ->
    (FreshSkolem i, SupplyFresh i, (succ i, wl, is))

addToWorkList :: WorkList -> Solver ()
addToWorkList newWork =
  update $ \(i, workList, inertSet) ->
    ((), AddToWorkList newWork,               --  it is important to *prepend* to the worklist here
     (i, prepend newWork workList, inertSet)) --  [Prepend New Work to the Work List]

{-

Note [Prepend New Work to the Work List]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A loop in the solver can be created if we *postpend* new work to the work list rather than
prepending it. In this case, the following input to the solver will cause it to loop:

Work List: a ~ b, b ~ c, c ~ a

Why? Here's a trace of what happens. (Remember that in the trace below, AddToWorkList is
putting the new work item(s) at the *end* of the work list.)

+------------------------------------------+-----------------------+-------------+
|       Step                               |  Work List            |  Inert Set  |
+------------------------------------------+-----------------------+-------------+
|   1.  AddToWorkList [a ~ b,b ~ c,c ~ a]  |  a ~ b, b ~ c, c ~ a  |             |
|   2.  NextWorkItem a ~ b                 |  b ~ c, c ~ a         |             |
|   3.  KickOutWith a ~ b                  |  b ~ c, c ~ a         |  a ~ b      |  <--- look at the state here
|   4.  AddToWorkList []                   |  b ~ c, c ~ a         |  a ~ b      |
|   5.  NextWorkItem b ~ c                 |  c ~ a                |  a ~ b      |
|   6.  KickOutWith b ~ c                  |  c ~ a                |  b ~ c      |
|   7.  AddToWorkList [a ~ b]              |  c ~ a, a ~ b         |  b ~ c      |
|   8.  NextWorkItem c ~ a                 |  a ~ b                |  b ~ c      |
|   9.  KickOutWith c ~ a                  |  a ~ b                |  c ~ a      |
|  10.  AddToWorkList [b ~ c]              |  a ~ b, b ~ c         |  c ~ a      |
|  11.  NextWorkItem a ~ b                 |  b ~ c                |  c ~ a      |
|  12.  KickOutWith a ~ b                  |  b ~ c                |  a ~ b      |
|  13.  AddToWorkList [c ~ a]              |  b ~ c, c ~ a         |  a ~ b      |  <--- same state here!

-}

nextWorkItem :: Solver (Maybe Equality)
nextWorkItem = do
  update $ \case
    (i, (e : es), is) ->
      (Just e, NextWorkItem e, (i, es, is))
    (i, [], is) ->
      (Nothing, Success, (i, [], is))

typeError :: Equality -> Solver a
typeError (a :=: b) = Solver $ throwError (a :=/=: b)

timeout :: Solver a
timeout = Solver $ throwError TimeoutError

getInertSet :: Solver InertSet
getInertSet =
  gets $ \((_, _, is), _) -> is

applyCanonical :: Canonical -> Type -> Type
applyCanonical c t =
  case c of
    CanTyVar v' t' ->
      case t of
        TyVar v | v == v'   -> t'
        TyVar v | otherwise -> t
        TyApp a b ->
          TyApp (applyCanonical c a)
                (applyCanonical c b)
        TyFamApp (f, a) ->
          TyFamApp $ (f, applyCanonical c a)
        TyConst k -> TyConst k
    CanTyFam (f, a) r ->
      case t of
        TyFamApp (f', a') | f == f' && a == a' -> TyVar r
        _ -> t

fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f =
   fst . head
   . dropWhile (uncurry (/=))
   . (zip <$> id <*> tail)
   . iterate f

applyInertSet :: Type -> Solver Type
applyInertSet ty = do
  inertSet <- getInertSet
  let subst = flip (foldr applyCanonical) inertSet
  return (fixedPoint subst ty)

pullTypeFamilies :: Type -> Solver (Type, [Canonical])
pullTypeFamilies t =
  case t of
    TyFamApp (f, a) -> do
      x <- freshSkolem
      return (TyVar x, [CanTyFam (f, a) x])
    TyApp a b -> do
      (a', funcans1) <- pullTypeFamilies a
      (b', funcans2) <- pullTypeFamilies b
      return (TyApp a' b', funcans1 ++ funcans2)
    _ -> return (t, [])

zonk :: Type -> Solver Type
zonk = return

flatten :: Type -> Solver (Type, [Canonical])
flatten =
  firstM zonk <=< pullTypeFamilies <=< applyInertSet

canonicalize :: Equality -> Solver [Canonical]
canonicalize (t1 :=: t2) = do

  -- Flatten both types
  (t1', funcans1) <- flatten t1
  (t2', funcans2) <- flatten t2

  -- Remember what type error to throw if things go wrong
  let thisIsATypeError = typeError (t1' :=: t2')

  -- Examine the flattened equality
  postpend (funcans1 ++ funcans2) <$>  -- FunCans have to come *after* the canonicalized thing
    case t1' of                        -- [Ordered Processing of Flattening Results]
      TyVar a ->
        case t2' of
          TyVar b | a == b -> return []    -- a ~ a is useless
          _ -> return [CanTyVar a t2]      -- a ~ t is already canonical
      TyApp s1 s2 ->
        case t2' of
          TyApp s3 s4 -> do                -- for s1 s2 ~ s3 s4,
            addToWorkList [s2 :=: s4]      -- add s2 ~ s4 to the work list for later
            canonicalize (s1 :=: s3)       -- and canonicalize s1 ~ s3
          TyVar b ->
            return [CanTyVar b t1]         -- for s1 s2 ~ a, flip it to make canonical
          _ -> thisIsATypeError            --     s1 s2 ~ _ for anything else is an error
      TyConst k ->
        case t2 of
          TyConst k' | k == k'   -> return []         -- two ground types are equal if they... are equal
          TyConst k' | otherwise -> thisIsATypeError  -- and they are not equal if they... are not
          TyVar b ->
            return [CanTyVar b t1]         -- for k ~ a, flip it to make canonical
          TyApp _ _ -> thisIsATypeError    -- k ~ _ _ is a type error
          TyFamApp tfa -> error $ "This should have been flattened!" ++ show tfa
      TyFamApp tfa -> error $ "This should have been flattened!" ++ show tfa

{-

Note [Ordered Processing of Flattening Results]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When we flatten, we receive as a result both a flattened type, and a list of "FunCans":
canonical forms of type family applications whose right hand sides are type variables.
For termination of the solver, we must process emitted FunCans *after* processing the
canonicalized equality whose creation led to their emission.

Why? Note that a FunCan, of the form F(t) = a, contains a type family application
(of course) in its left hand side. If we process this before the canonicalized equality
giving rise to it, then we will proceed to flatten it again, which gives us (for fresh b),
F(t) ~ a, b ~ a. We successfully insert F(t) ~ a into the inert set, but right after,
we process b ~ a, which kicks out F(t) ~ a by rule (K3a).

Every loop around the solver will merely add another transitive link to the inert set.
Below is a trace of this behavior:

+--------------------------------------+-----------------+---------------------------------------+
|  Step                                |  Work List      |  Inert Set                            |
+--------------------------------------+-----------------+---------------------------------------+
|   1.  AddToWorkList [F(Int) ~ Bool]  |  F(Int) ~ Bool  |                                       |
|   2.  NextWorkItem F(Int) ~ Bool     |                 |                                       |
|   3.  SupplyFresh 0                  |                 |                                       |
|   4.  KickOutWith F(Int) ~ [0]       |                 |  F(Int) ~ [0]                         |
|   5.  AddToWorkList []               |                 |  F(Int) ~ [0]                         |
|   6.  KickOutWith [0] ~ Bool         |                 |  [0] ~ Bool                           |
|   7.  AddToWorkList [F(Int) ~ [0]]   |  F(Int) ~ [0]   |  [0] ~ Bool                           |
|   8.  NextWorkItem F(Int) ~ [0]      |                 |  [0] ~ Bool                           |
|   9.  SupplyFresh 1                  |                 |  [0] ~ Bool                           |
|  10.  KickOutWith F(Int) ~ [1]       |                 |  F(Int) ~ [1], [0] ~ Bool             |
|  11.  AddToWorkList []               |                 |  F(Int) ~ [1], [0] ~ Bool             |
|  12.  KickOutWith [1] ~ [0]          |                 |  [1] ~ [0], [0] ~ Bool                |
|  13.  AddToWorkList [F(Int) ~ [1]]   |  F(Int) ~ [1]   |  [1] ~ [0], [0] ~ Bool                |
|  14.  NextWorkItem F(Int) ~ [1]      |                 |  [1] ~ [0], [0] ~ Bool                |
|  15.  SupplyFresh 2                  |                 |  [1] ~ [0], [0] ~ Bool                |
|  16.  KickOutWith F(Int) ~ [2]       |                 |  F(Int) ~ [2], [1] ~ [0], [0] ~ Bool  |
|  17.  AddToWorkList []               |                 |  F(Int) ~ [2], [1] ~ [0], [0] ~ Bool  |
|  18.  KickOutWith [2] ~ [1]          |                 |  [2] ~ [1], [1] ~ [0], [0] ~ Bool     |
|  19.  AddToWorkList [F(Int) ~ [2]]   |  F(Int) ~ [2]   |  [2] ~ [1], [1] ~ [0], [0] ~ Bool     |

Note that this issue never violates the inert set invariant at any specific moment:
the inert set indeed remains an inert generalized substitution; however, at every step,
the number of iterations required to compute its fixed point *grows* by one.

Another solution you might think of: what if we take the produced FunCans and place
them back in the work list to process later? This too, leads to a (quite similar) loop!
When we reach the FunCan in the work list that we previously produced, we will flatten it,
making a new fresh type variable and postponing our real processing of this FunCan again.

Below is a trace of this behavior:

+--------------------------------------+-----------------+------------------------------------+
|  Step                                |  Work List      |  Inert Set                         |
+--------------------------------------+-----------------+------------------------------------+
|   1.  AddToWorkList [F(Int) ~ Bool]  |  F(Int) ~ Bool  |                                    |
|   2.  NextWorkItem F(Int) ~ Bool     |                 |                                    |
|   3.  SupplyFresh 0                  |                 |                                    |
|   4.  AddToWorkList [F(Int) ~ [0]]   |  F(Int) ~ [0]   |                                    |
|   5.  KickOutWith [0] ~ Bool         |  F(Int) ~ [0]   |  [0] ~ Bool                        |
|   6.  AddToWorkList []               |  F(Int) ~ [0]   |  [0] ~ Bool                        |
|   7.  NextWorkItem F(Int) ~ [0]      |                 |  [0] ~ Bool                        |
|   8.  SupplyFresh 1                  |                 |  [0] ~ Bool                        |
|   9.  AddToWorkList [F(Int) ~ [1]]   |  F(Int) ~ [1]   |  [0] ~ Bool                        |
|  10.  KickOutWith [1] ~ [0]          |  F(Int) ~ [1]   |  [1] ~ [0], [0] ~ Bool             |
|  11.  AddToWorkList []               |  F(Int) ~ [1]   |  [1] ~ [0], [0] ~ Bool             |
|  12.  NextWorkItem F(Int) ~ [1]      |                 |  [1] ~ [0], [0] ~ Bool             |
|  13.  SupplyFresh 2                  |                 |  [1] ~ [0], [0] ~ Bool             |
|  14.  AddToWorkList [F(Int) ~ [2]]   |  F(Int) ~ [2]   |  [1] ~ [0], [0] ~ Bool             |
|  15.  KickOutWith [2] ~ [1]          |  F(Int) ~ [2]   |  [2] ~ [1], [1] ~ [0], [0] ~ Bool  |
|  16.  AddToWorkList []               |  F(Int) ~ [2]   |  [2] ~ [1], [1] ~ [0], [0] ~ Bool  |
|  17.  NextWorkItem F(Int) ~ [2]      |                 |  [2] ~ [1], [1] ~ [0], [0] ~ Bool  |
|  18.  SupplyFresh 3                  |                 |  [2] ~ [1], [1] ~ [0], [0] ~ Bool  |
|  19.  AddToWorkList [F(Int) ~ [3]]   |  F(Int) ~ [3]   |  [2] ~ [1], [1] ~ [0], [0] ~ Bool  |

The moral of the story: we can't be too eager or too lazy in our processing of emitted
FunCans from flattening: if we process them first, we loop; if we defer them for later
processing, we loop. We must hold onto them and process them immediately (without further
flattening!) after we process the result of canonicalization.

-}

-- Based upon [Extending the inert equalities] in TcSMonad
shouldKickOut :: Canonical -> Canonical -> Bool
(uncanonicalize -> (a :=: t)) `shouldKickOut` (uncanonicalize -> (b :=: s)) =
  or [ a == b    -- (K1) specialized to givens
     , False     -- (K2) is trivial via (K2b) for givens
     , s == a    -- (K3a) since we're only thinking about nominal currently
     ]

kickOutWith :: Canonical -> Solver [Canonical]
kickOutWith c = do
  (kickedOut, newInertSet) <- partition (c `shouldKickOut`) <$> getInertSet
  update $ \(i, wl, _) ->
    (kickedOut, KickOutWith c, (i, wl, c : newInertSet))

solverStep :: Equality -> Solver ()
solverStep equality =
  canonicalize equality >>= mapM_
    (addToWorkList . (map uncanonicalize) <=< kickOutWith)

solveToDepth :: Integer -> [Equality] -> Solver [Canonical]
solveToDepth depth input =
  addToWorkList input >> solverLoop depth >> getInertSet
  where
    solverLoop 0 = timeout
    solverLoop d =
      nextWorkItem >>= \case
        Nothing -> return ()
        Just e  -> solverStep e >> solverLoop (d - 1)



-- MISCELLANEOUS

prepend :: [a] -> [a] -> [a]
prepend = (++)

postpend :: [a] -> [a] -> [a]
postpend = flip (++)

firstM :: Monad m => (a -> m c) -> (a, b) -> m (c, b)
firstM f (x, y) = liftM (\x' -> (x', y)) (f x)

padL :: Int -> String -> String
padL n s
    | length s < n = s ++ replicate (n - length s) ' '
    | otherwise    = s

padR :: Int -> String -> String
padR n s
    | length s < n = replicate (n - length s) ' ' ++ s
    | otherwise    = s

-- Pretty-printing the log of a solver run in an ASCII table

formatHistory :: History -> [String]
formatHistory history =
  let histLength = length history
      numberingWidth = 3 + length (show histLength)
      (map show -> actions,
       unzip3 -> (map show -> counts,
                  map (intercalate ", " . map show) -> lists,
                  map (intercalate ", " . map show) -> sets)) = unzip history
      actionsWidth = maximum (map length actions) `max` (length $ columnNames !! 0)
      countsWidth  = maximum (map length counts)
      listsWidth   = maximum (map length lists)   `max` (length $ columnNames !! 1)
      setsWidth    = maximum (map length sets)    `max` (length $ columnNames !! 2)
      columnWidths = [numberingWidth + actionsWidth, listsWidth, setsWidth]
      columnNames  = ["Step", "Work List", "Inert Set"]
      header       = "|  " ++ intercalate "  |  " (zipWith padL columnWidths columnNames) ++ "  |"
      horizontal   = "+--" ++ intercalate "--+--" (map (flip replicate '-') columnWidths) ++ "--+"
  in (++ [horizontal]) . ([horizontal, header, horizontal] ++)
     . zipWith (curry (uncurry (++) . ((("|  " ++) . padR numberingWidth . (++ ".  ") . show) *** id))) [1..]
     . reverse $
       ((zipWith4 $
            \(padL actionsWidth -> action)
             (padL countsWidth  -> count)
             (padL listsWidth   -> list)
             (padL setsWidth    -> set) ->
                action ++ "  |  " ++ list ++ "  |  " ++ set ++ "  |")
          actions counts lists sets)

printRunWithDepth :: Integer -> [Equality] -> IO ()
printRunWithDepth n input = do
  let (solution, history) = (runSolverLogging . solveToDepth n) input
  putStrLn ""
  print solution
  putStrLn ""
  forM_ (formatHistory history) putStrLn

{-

Note [Guide to Printed Notation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Variables
---------

+ source variables printed as written
+ solver-generated skolems printed as [#]
+ solver-generated unification variables printed as {#}

Types
-----

+ constants printed as written
+ variables printed as above
+ applications printed as space-separated, like in Haskell
+ type family applications printed in parenthesized style, e.g. F(t)

Equalities
----------

+ printed with a twiddle (~)
+ canonical equalities are printed the same as non-canonical ones

Everything else is auto-derived.

-}

-- PARSING

-- We define a parser for [Equality] and a convenient quasi-quoter for it:
-- For instance, [constraints| x ~ y, y ~ x |] desugars into
-- [TyVar (SrcVar "x") :=: TyVar (SrcVar "y"), TyVar (SrcVar "y") :=: TyVar (SrcVar "x")]

identifierStartingWith :: Parser Char -> Parser String
identifierStartingWith parser =
  ((:) <$> parser
       <*> many (alphaNumChar <|> char '_'))

parens, spaces :: Parser a -> Parser a
parens = between (char '(') (char ')')
spaces = between space space

parseConst :: Parser Const
parseConst = Const <$> identifierStartingWith upperChar

parseVar :: Parser Var
parseVar = SrcVar <$> identifierStartingWith lowerChar

parseTyFam :: Parser TyFam
parseTyFam = TyFam <$> identifierStartingWith upperChar

parseType :: Parser Type
parseType =
  (foldl1 TyApp <$>) . flip sepEndBy space $
    try (TyFamApp <$> ((,) <$> parseTyFam
                           <*> parens (spaces parseType)))
    <|> TyConst <$> parseConst
    <|> TyVar <$> parseVar
    <|> parens (spaces parseType)

parseEquality :: Parser Equality
parseEquality = do
  [t1, t2] <- parseType `sepBy1` spaces (char '~')
  return (t1 :=: t2)

parseEqualities :: Parser [Equality]
parseEqualities = parseEquality `sepEndBy` spaces (char ',')

constraints :: QuasiQuoter
constraints = QuasiQuoter
           { quoteExp = \str -> do
               Loc { loc_filename = file, loc_start = (row, col) } <- location
               let pos = newPos file row col
               c <- runIO $ parseIO (setPosition pos *> space *> parseEqualities) file str
               dataToExpQ (const Nothing) c
           , quotePat = undefined
           , quoteType = undefined
           , quoteDec = undefined }

parseIO :: Parser a -> String -> String -> IO a
parseIO parser file str =
  case runParser parser file str of
    Right a -> return a
    Left err -> ioError (userError (show err))

-- PRINTING
-- We print things prettily; right now, we use Show for this.

instance Show Var where
  show v = case v of
    SrcVar s -> s
    FreshSkolem i -> "[" ++ show i ++ "]"
    UnifVar i -> "{" ++ show i ++ "}"

isCompound :: Type -> Bool
isCompound t = case t of
  TyApp _ _  -> True
  TyFamApp _ -> True
  _ -> False

showWithParens :: Show a => Bool -> a -> String
showWithParens True  a = "(" ++ show a ++ ")"
showWithParens False a = show a

instance Show Type where
  show t = case t of
    TyConst k -> show k
    TyVar v -> show v
    TyApp t1 t2 -> show t1 ++ " " ++ showWithParens (isCompound t2) t2
    TyFamApp (f, a) -> show f ++ "(" ++ show a ++ ")"

instance Show Const where
  show (Const s) = s

instance Show TyFam where
  show (TyFam s) = s

instance Show Equality where
  show (t1 :=: t2) = show t1 ++ " ~ " ++ show t2

deriving instance Show SolverError

instance Show Canonical where
  show = show . uncanonicalize

-- Deriving Eq and Data for things...

deriving instance Eq Var
deriving instance Eq Type
deriving instance Eq Equality
deriving instance Eq SolverError
deriving instance Eq Canonical

deriving instance Data Var
deriving instance Data Const
deriving instance Data TyFam
deriving instance Data Type
deriving instance Data Equality
