{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Bits (Bits, (.&.), (.|.), xor)
import Data.Foldable (foldlM)
import Data.Function (on)
import Data.List (find, foldl', intercalate, stripPrefix)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import GHC.Exts (IsString(..))
import qualified Data.Map as Map

main = do
  print fibProc
  print (invert fibProc)
  mapM_ (print . snd) . Map.toList . envGlobals =<< interpret mempty fib

fib :: Prog
fib = Prog
  [ mainProc
  , fibProc
  ]

mainProc :: Proc
mainProc = Proc "main" [] $ StatSeq
  [ StatVar "x1" Scalar
  , StatVar "x2" Scalar
  , StatVar "n" Scalar
  , StatMod "n" OpAdd 20
  , StatCall "fib" [Out "x1", Out "x2", In "n"]
  , StatTrace "n"
  , StatTrace "x2"
  , StatVar "y1" Scalar
  , StatVar "y2" Scalar
  , StatVar "m" Scalar
  , StatMod "y1" OpAdd 5
  , StatMod "y2" OpAdd 8
  , StatUncall "fib" [In "y1", In "y2", Out "m"]
  , StatTrace "y2"
  , StatTrace "m"
  ]

fibProc = Proc "fib" [("x1", Scalar), ("x2", Scalar), ("n", Scalar)]
  $ StatIf (ExprOp OpEqual (ExprVar "n") 0)
    (StatSeq
      [ StatMod "x1" OpAdd 1
      , StatMod "x2" OpAdd 1
      ])
    (StatSeq
      [ StatMod "n" OpSub 1
      , StatCall "fib" [Out "x1", Out "x2", Out "n"]
      , StatMod "x1" OpAdd "x2"
      -- swap
      , StatSwap "x1" "x2"
      , StatTrace "n"
      , StatTrace "x2"
      ])
    (ExprOp OpEqual "x1" "x2")

{-
procedure fib(int x1, int x2, int n)
    if n = 0 then
        x1 += 1
        x2 += 1
    else
        n -= 1
        call fib(x1, x2, n)
        x1 += x2
        x1 <=> x2
    fi x1 = x2

procedure main()
    int x1
    int x2
    int n
    n += 4
    call fib(x1, x2, n)
-}

data Env = Env
  { envGlobals :: Map Name Proc
  , envLocals :: [Map Name Val]
  } deriving (Show)

instance Monoid Env where
  mempty = Env
    { envGlobals = mempty
    , envLocals = [mempty]
    }
  mappend a b = Env
    { envGlobals = (mappend `on` envGlobals) a b
    , envLocals = (mappend `on` envLocals) a b
    }

interpret :: Env -> Prog -> IO Env
interpret env0 (Prog procs) = case find matching procs of
  Just (Proc _ _ body) -> exec env body
  _ -> pure env0
  where
    matching (Proc "main" [] _) = True
    matching _ = False
    env = env0
      { envGlobals = foldr (uncurry Map.insert) (envGlobals env0)
        [(name, proc) | proc@(Proc name _ _) <- procs]
      }

envGetLocal :: Name -> Env -> Maybe Val
envGetLocal name env = case envLocals env of
  [] -> error "get: no scope"
  scope : _ -> Map.lookup name scope

envGetGlobal :: Name -> Env -> Maybe Proc
envGetGlobal name env = Map.lookup name (envGlobals env)

envSetLocal :: Name -> Val -> Env -> Env
envSetLocal name val env = case envLocals env of
  [] -> error "set: no scope"
  scope : scopes -> env { envLocals = Map.insert name val scope : scopes }

envEnter :: Env -> Env
envEnter env = env { envLocals = mempty : envLocals env }

envLeave :: Env -> Env
envLeave env = case envLocals env of
  [] -> error "leave: no scope"
  _ : scopes -> env { envLocals = scopes }

envReturn :: [(Name, Arg)] -> Env -> Env
envReturn args env = case envLocals env of
  current : parent : rest -> env
    { envLocals = foldr ret parent args : rest }
    where
      ret (name, Out name') scope = case Map.lookup name current of
        Just val -> Map.insert name' val scope
        Nothing -> error "returning nonexistent variable"
      ret (_, In _) scope = scope
  _ -> error "return: no scope"

exec :: Env -> Stat -> IO Env
exec env = go
  where
  go stat = case stat of

    StatMod name op expr -> do
      let val = fromMaybe 0 (envGetLocal name env)
      val' <- eval env expr
      val'' <- applyOp (OpModOp op) val val'
      pure (envSetLocal name val'' env)

    StatModArray name subscript op expr -> error "TODO: mod array"

    StatIf pre true false post -> do
      pre' <- eval env pre
      (wasTrue, env') <- case pre' of
        ValConst 0 -> (,) False <$> exec env false
        _ -> (,) True <$> exec env true
      post' <- eval env' post
      case post' of
        ValConst 0 | not wasTrue -> return ()
        _ | wasTrue -> return ()
        _ -> error $ concat
          [ "if: postcondition "
          , if wasTrue then "" else "!("
          , show post
          , if wasTrue then "" else ")"
          , " not met; env: "
          , show env'
          ]
      return env'

    StatLoop pre body1 body2 post -> error "TODO: loop"

    StatPush stack var -> error "TODO: push"

    StatPop stack var -> error "TODO: pop"

    StatLocal name1 type1 pre body name2 type2 post -> error "TODO: local"

    StatCall name args -> case envGetGlobal name env of
      Just (Proc _ params body) -> execProc env (map fst params) args body
      Nothing -> error "call to nonexistent proc"

    StatUncall name args -> case envGetGlobal name env of
      Just (Proc _ params body)
        -> execProc env (map fst params) args (invert body)
      Nothing -> error "uncall to nonexistent proc"

    StatSkip -> error "TODO: skip"

    StatSeq stats -> foldlM exec env stats

    StatTrace expr -> do
      val <- eval env expr
      putStrLn $ concat [show expr, " => ", show val]
      pure env

    StatSwap a b -> go (StatSeq
      [ StatMod a OpXor (ExprVar b)
      , StatMod b OpXor (ExprVar a)
      , StatMod a OpXor (ExprVar b)
      ])

    StatVar name type_ -> let
      val = case type_ of
        Scalar -> ValConst 0
        Array{} -> ValArray []
      in pure (envSetLocal name val env)

inOut :: Arg -> Arg
inOut (In name) = Out name
inOut (Out name) = In name

execProc :: Env -> [Name] -> [Arg] -> Stat -> IO Env
execProc env params args body = do
  args' <- traverse (eval env . ExprVar . argName) args
  let
    env' = foldr (uncurry envSetLocal)
      (envEnter env) (zip params args')
  envReturn (zip params args) <$> exec env' body

class Invertible a where
  invert :: a -> a

instance Invertible Stat where
  invert stat = case stat of

    StatMod name op expr
      -> StatMod name (invert op) expr

    StatModArray name subscript op expr
      -> StatModArray name subscript (invert op) expr

    StatIf pre true false post
      -> StatIf post (invert true) (invert false) pre

    StatLoop pre body1 body2 post
      -> StatLoop post (invert body1) (invert body2) pre

    StatPush stack var
      -> StatPop stack var

    StatPop stack var
      -> StatPush stack var

    StatLocal name1 type1 expr1 body name2 type2 expr2
      -> StatLocal name2 type2 expr2 (invert body) name1 type1 expr1

    StatCall name args
      -> StatUncall name args

    StatUncall name args
      -> StatCall name args

    StatSkip -> stat

    StatSeq stats -> StatSeq (map invert (reverse stats))

    StatTrace{} -> stat

    StatSwap{} -> stat

    StatVar{} -> stat  -- TODO: remove?

applyOp :: Op -> Val -> Val -> IO Val
applyOp op a b = case op of
  OpModOp modOp -> case modOp of
    OpAdd -> case (a, b) of
      (ValConst a', ValConst b') -> pure (ValConst (a' + b'))
      _ -> error "TODO: add"
    OpSub -> case (a, b) of
      (ValConst a', ValConst b') -> pure (ValConst (a' - b'))
      _ -> error "TODO: sub"
    OpXor -> case (a, b) of
      (ValConst a', ValConst b') -> pure (ValConst (a' `xor` b'))
      _ -> error "TODO: xor"
  OpMul -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (a' * b'))
    _ -> error "TODO: mul"
  OpDiv -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (a' `div` b'))
    _ -> error "TODO: div"
  OpRem -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (a' `rem` b'))
    _ -> error "TODO: rem"
  OpAnd -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (a' .&. b'))
    _ -> error "TODO: and"
  OpOr -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (a' .|. b'))
    _ -> error "TODO: or"
  OpAndThen -> error "TODO: and then"
  OpOrElse -> error "TODO: or else"
  OpLess -> error "TODO: <"
  OpGreater -> error "TODO: >"
  OpEqual -> case (a, b) of
    (ValConst a', ValConst b') -> pure (ValConst (Const (fromIntegral (fromEnum (a' == b')))))
    _ -> error "TODO: ="
  OpNotEqual -> error "TODO: <>"
  OpNotGreater -> error "TODO: <="
  OpNotLess -> error "TODO: >="

eval :: Env -> Expr -> IO Val
eval env = go
  where
    go expr = case expr of
      ExprVal val -> pure val
      ExprVar name -> case envGetLocal name env of
        Just val -> pure val
        Nothing -> pure 0
      ExprIndex name expr -> case envGetLocal name env of
        Just (ValArray vals) -> do
          ValConst (Const val) <- go expr
          pure (vals !! fromInteger val)
        _ -> error "indexing non-array"
      ExprOp op a b -> do
        a' <- go a
        b' <- go b
        applyOp op a' b'
      ExprEmpty name -> case envGetLocal name env of
        Just (ValArray []) -> pure 1
        _ -> pure 0
      ExprTop name -> case envGetLocal name env of
        Just (ValArray (x : _)) -> pure x
        _ -> error "top of empty array or non-array"

data Prog = Prog [Proc]

data Dest = DestScalar Name | DestArray Name Const

data Type
  = Scalar
  | Array Type (Maybe Size)

newtype Size = Size Int

instance Show Size where
  show (Size size) = show size

instance Show Type where
  show type_ = case type_ of
    Scalar -> "#"
    Array elementType mSize -> case mSize of
      Just size -> concat [show elementType, "^", show size]
      Nothing -> concat [show elementType, "*"]

data Proc = Proc Name [(Name, Type)] Stat

instance Invertible Proc where
  invert (Proc (Name name) params body)
    = case stripPrefix (reverse "_inv") (reverse name) of
      Just prefix -> Proc (Name (reverse prefix)) params (invert body)
      Nothing -> Proc (Name (name ++ "_inv")) params (invert body)

instance Show Proc where
  show (Proc name params body) = concat
    [ "procedure "
    , show name
    , "("
    , intercalate ", " (map showParam params)
    , ") "
    , show body
    ]
    where
      showParam (name, type_) = concat [show name, " : ", show type_]

data Stat
  = StatMod Name ModOp Expr
  | StatModArray Name Expr ModOp Expr
  | StatIf Expr Stat Stat Expr
  | StatLoop Expr Stat Stat Expr
  | StatPush Name Name
  | StatPop Name Name
  | StatLocal Name Type Expr Stat Name Type Expr
  | StatCall Name [Arg]
  | StatUncall Name [Arg]
  | StatSkip
  | StatSeq [Stat]
  | StatTrace Expr
  | StatSwap Name Name
  | StatVar Name Type

data Arg
  = In { argName :: Name }
  | Out { argName :: Name }

instance Show Arg where
  show arg = case arg of
    In name -> unwords ["in", show name]
    Out name -> unwords ["out", show name]

instance Show Stat where
  show stat = case stat of
    StatMod name op expr
      -> concat [show name, " ", show op, "= ", show expr, ";"]
    StatModArray name subscript op expr -> concat
      [ show name
      , "["
      , show subscript
      , "] "
      , show op
      , "= "
      , show expr
      , ";"]
    StatIf pre true false post -> concat
      [ "if "
      , show pre
      , " then "
      , show true
      , " else "
      , show false
      , " endif "
      , show post
      , ";"
      ]
    StatLoop pre body1 body2 post -> concat
      [ "from "
      , show pre
      , " do "
      , show body1
      , " loop "
      , show body2
      , " until "
      , show post
      , ";"
      ]
    StatPush stack var -> concat ["push(", show stack, ", ", show var, ");"]
    StatPop stack var -> concat ["push(", show stack, ", ", show var, ");"]
    StatLocal name1 type1 pre body name2 type2 post -> concat
      [ "local "
      , show name1
      , " : "
      , show type1
      , " = "
      , show pre
      , " "
      , show body
      , " delocal "
      , show name2
      , " : "
      , show type2
      , " = "
      , show post
      , ";"
      ]
    StatCall name args -> concat
      [ "call "
      , show name
      , "("
      , intercalate ", " (map show args)
      , ");"
      ]
    StatUncall name args -> concat
      [ "uncall "
      , show name
      , "("
      , intercalate ", " (map show args)
      , ");"
      ]
    StatSkip -> "skip;"
    StatSeq stats -> concat ["{ ", unwords (map show stats), " }"]
    StatTrace expr -> concat ["trace(", show expr, ");"]
    StatSwap a b -> concat [show a, " <=> ", show b, ";"]
    StatVar name type_ -> concat ["var ", show name, " : ", show type_, ";"]

data Expr
  = ExprVal Val
  | ExprVar Name
  | ExprIndex Name Expr
  | ExprOp Op Expr Expr
  | ExprEmpty Name
  | ExprTop Name

instance Num Expr where
  fromInteger = ExprVal . fromInteger

instance IsString Expr where
  fromString = ExprVar . fromString

instance Show Expr where
  showsPrec p expr = case expr of
    ExprVal val -> shows val
    ExprVar name -> shows name
    ExprIndex name expr
      -> shows name . showString "[" . shows expr . showString "]"
    ExprOp op a b -> let
      p' = opPrec op
      in showParen (opPrec op < p)
        $ showsPrec p' a
        . showChar ' '
        . shows op
        . showChar ' '
        . showsPrec p' b
    ExprEmpty name -> showString "empty(" . shows name . showChar ')'
    ExprTop name -> showString "top(" . shows name . showChar ')'

data Val
  = ValConst Const
  | ValArray [Val]

instance Num Val where
  fromInteger = ValConst . Const
  ValConst a + ValConst b = ValConst (a + b)
  _ + _ = error "cannot add arrays"
  ValConst a - ValConst b = ValConst (a - b)
  _ - _ = error "cannot subtract arrays"
  ValConst a * ValConst b = ValConst (a * b)
  _ * _ = error "cannot multiply arrays"
  abs (ValConst a) = ValConst (abs a)
  abs _ = error "cannot take absolute value of array"
  negate (ValConst a) = ValConst (negate a)
  negate _ = error "cannot negate array"
  signum (ValConst a) = ValConst (signum a)
  signum _ = error "cannot take sign of array"

instance Show Val where
  show val = case val of
    ValConst const -> show const
    ValArray vals -> concat ["[", intercalate ", " (map show vals), "]"]

newtype Const = Const Integer
  deriving (Bits, Enum, Eq, Integral, Num, Ord, Real)

instance Show Const where
  show (Const const) = show const

data Op
  = OpModOp ModOp
  | OpMul
  | OpDiv
  | OpRem
  | OpAnd
  | OpOr
  | OpAndThen
  | OpOrElse
  | OpLess
  | OpGreater
  | OpEqual
  | OpNotEqual
  | OpNotGreater
  | OpNotLess

instance Show Op where
  show op = case op of
    OpModOp modOp -> show modOp
    OpMul -> "*"
    OpDiv -> "/"
    OpRem -> "%"
    OpAnd -> "&"
    OpOr -> "|"
    OpAndThen -> "&&"
    OpOrElse -> "||"
    OpLess -> "<"
    OpGreater -> ">"
    OpEqual -> "="
    OpNotEqual -> "<>"
    OpNotGreater -> "<="
    OpNotLess -> ">="

data ModOp
  = OpAdd
  | OpSub
  | OpXor

instance Show ModOp where
  show op = case op of
    OpAdd -> "+"
    OpSub -> "-"
    OpXor -> "^"

type Prec = Int

opPrec :: Op -> Prec
opPrec op = case op of
  OpModOp modOp -> modOpPrec modOp
  OpMul -> 7
  OpDiv -> 7
  OpRem -> 7
  OpAnd -> 7
  OpOr -> 7
  OpAndThen -> 3
  OpOrElse -> 2
  OpLess -> 4
  OpGreater -> 4
  OpEqual -> 4
  OpNotEqual -> 4
  OpNotGreater -> 4
  OpNotLess -> 4

modOpPrec :: ModOp -> Prec
modOpPrec op = case op of
  OpAdd -> 6
  OpSub -> 6
  OpXor -> 6

instance Invertible ModOp where
  invert op = case op of
    OpAdd -> OpSub
    OpSub -> OpAdd
    OpXor -> OpXor

newtype Name = Name String
  deriving (Eq, IsString, Ord)

instance Show Name where
  show (Name string) = string
