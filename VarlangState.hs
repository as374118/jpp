module VarlangState where

import           Data.Map                       ( Map
                                                , insert
                                                , lookup
                                                , size
                                                , fromList
                                                , empty
                                                , showTree
                                                , toList
                                                , filterWithKey
                                                , elems
                                                )
import           Data.List                      ( sort
                                                , find
                                                )
import           System.IO                      ( stderr
                                                , stdout
                                                , hPutStrLn
                                                )

import           AbsVarlang
import           ErrM

-- import InterpreterUtils

-- Type definitions
type Loc = Integer
type Env = Map Ident Loc
type Vals = Map Loc Val
type MyState = Err StateVL
type IntValOperation = Int -> Val -> Val

data Val = ValInt Int
         | ValBool Bool
         | ValChar Char
         | ValVoid
         | ValFun Type [Arg] [Stm]
         | ValList Type [Val]
         | ValDict (Map Val Val)
         | ValVar Ident Val
         | ValNone
    deriving (Eq, Ord, Show, Read)

data StateVL =  StateVL Env Vals HelpVars
    deriving (Eq, Ord, Show, Read)

data HelpVars = HelpVars Loc [String]
    deriving (Eq, Ord, Show, Read)

-- Help variables
trying_to_add_void_variable = "Trying to add void variable: "
variable_not_found = "Variable was not found in current state: "
type_mismath_runtime = "Runtime error: type mismatch | variable: "

startStateVL = Ok (StateVL Data.Map.empty Data.Map.empty (HelpVars 0 []))

-- Functions
addError :: String -> MyState -> MyState
addError msg state = case state of
    Ok  state -> Bad $ "last state before error: " ++ (show state) ++ "|||" ++ msg
    Bad s     -> Bad $ s ++ "|||" ++ msg

addToState :: Ident -> Val -> MyState -> MyState
addToState ident val state = case state of
    Ok (StateVL env vals (HelpVars lastLoc printQueue)) -> case val of
        ValVoid -> Bad trying_to_add_void_variable
        _       -> Ok $ StateVL (insert ident newLoc env) (insert newLoc val vals) newHelpVars
          where
            newLoc      = lastLoc + 1
            newHelpVars = (HelpVars newLoc printQueue)
    Bad s -> Bad s

getValFromState :: Ident -> MyState -> (Val, MyState)
getValFromState ident state = case (tryToGetValFromState ident state) of
    Just val -> (val, state)
    Nothing  -> (ValVoid, addError (variable_not_found ++ (show ident)) state)

tryToGetValFromState :: Ident -> MyState -> Maybe Val
tryToGetValFromState ident state = snd (tryToGetValInfoForIdent ident state)


tryToGetValInfoForIdent :: Ident -> MyState -> (Maybe Loc, Maybe Val)
tryToGetValInfoForIdent ident state = case state of
    Ok (StateVL env vals _) -> case Data.Map.lookup ident env of
        Just loc -> (Just loc, Data.Map.lookup loc vals)
        Nothing  -> (Nothing, Nothing)
    Bad s -> (Nothing, Nothing)

changeValInState :: Ident -> Val -> MyState -> MyState
changeValInState ident val state = case (tryToGetValInfoForIdent ident state) of
    (Just loc, Just oldVal) -> case state of
        Ok  (StateVL env vals i) -> Ok (StateVL env (Data.Map.insert loc val vals) i)
        Bad s                    -> state
    _ -> Bad $ variable_not_found ++ (show ident) ++ " State: " ++ (show state)


-- This function will remove all useless pairs from vals
-- Useless pairs are ones that don't have references from env
cleanState :: MyState -> MyState
cleanState state = case state of
    Ok  (StateVL env vals hv) ->
        Ok (StateVL env newVals hv) where
            newVals = Data.Map.filterWithKey (\k _ -> elem k (Data.Map.elems env)) vals
    Bad s                    -> Bad s

-- function for printing -- reverse list before printing
printStr :: String -> MyState -> MyState
printStr str state = case state of
    Ok (StateVL env vals (HelpVars i printQueue)) ->
        Ok (StateVL env vals (HelpVars i $ str : printQueue))
    Bad s -> state

printVal :: Val -> MyState -> MyState
printVal val = printStr (toStringVal val)


toStringVal :: Val -> String
toStringVal val = case val of
    ValInt  i   -> show i
    ValBool b   -> show b
    ValChar c   -> [c]
    ValList _ l -> show l
    something   -> show something


checkValTypes :: Val -> Val -> Bool
checkValTypes (ValInt  _    ) (ValInt  _    ) = True
checkValTypes (ValBool _    ) (ValBool _    ) = True
checkValTypes (ValChar _    ) (ValChar _    ) = True
checkValTypes (ValFun t1 _ _) (ValFun t2 _ _) = True
checkValTypes (ValList t1 _ ) (ValList t2 _ ) = t1 == t2
checkValTypes (ValDict _    ) (ValDict _    ) = True
checkValTypes (ValVar _ _   ) (ValVar _ _   ) = True
checkValTypes _               _               = False

getDefaultVal :: Type -> Val
getDefaultVal val = case val of
    Int                  -> ValInt 0
    Bool                 -> ValBool False
    Char                 -> ValChar '\0'
    Void                 -> ValVoid
    Fun retType argTypes -> ValFun retType [] []
    List t               -> ValList t []
    Dict t1 t2           -> ValDict Data.Map.empty
    Var []               -> ValVoid
    Var _                -> ValVar (Ident "") ValVoid

valToExp :: Val -> Exp
valToExp val = case val of
    ValInt i -> EInt (toInteger i)
    ValBool p -> if p then EValTrue else EValFalse
    ValChar c -> EChar c
    ValFun _ args stmts -> EFun args stmts
    ValList _ l -> EList (map valToExp l)
    ValVar ident val -> EVar ident (valToExp val)
    ValDict m -> EDict (map (\(k, v) -> EDictD (valToExp k) (valToExp v)) (Data.Map.toList m))
    _ -> EInt 0


isList :: Val -> Bool
isList (ValList _ _) = True
isList _             = False

getListElType :: Val -> Type
getListElType (ValList t _) = t

getValList :: Val -> [Val]
getValList (ValList _ l) = l

getTypeForVals :: [Val] -> Type
getTypeForVals []      = Void
getTypeForVals (x : _) = getValType x

getValType :: Val -> Type
getValType x = case x of
    ValInt  _    -> Int
    ValBool _    -> Bool
    ValChar _    -> Char
    ValVoid      -> Void
    ValFun t _ _ -> Fun t []
    ValList t _  -> List t
    ValDict _    -> Dict Void Void
    ValVar _ _   -> Var []

getPossibleFunStmts :: Stm -> [Stm]
getPossibleFunStmts stm = case stm of
    StmBlock stmts        -> stmts
    StmIf _ stm           -> [stm]
    StmIfElse _ stm1 stm2 -> [stm1, stm2]
    StmWhile _ stm        -> [stm]
    StmFor _ _ stmts      -> stmts
    StmMatch _ _          -> []
    _                     -> []

valIntOperation :: (Int -> Int -> Int) -> IntValOperation
valIntOperation fun int2 (ValInt int) = ValInt (fun int int2)

incrIntVal :: IntValOperation
incrIntVal = valIntOperation (+)

decrIntVal :: IntValOperation
decrIntVal = valIntOperation (-)

divIntVal :: IntValOperation
divIntVal = valIntOperation div

multIntVal :: IntValOperation
multIntVal = valIntOperation (*)

modIntVal :: IntValOperation
modIntVal = valIntOperation mod

isNone :: Val -> Bool
isNone ValNone = True
isNone _       = False

negInt :: Int -> Int
negInt i = -i
