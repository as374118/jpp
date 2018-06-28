module TypeChecker where

import           Data.Map                       ( Map
                                                , insert
                                                , lookup
                                                , size
                                                , fromList
                                                , empty
                                                , showTree
                                                )
import           Data.List                      ( sort
                                                , find
                                                )

import           AbsVarlang
import           VarlangState
import           ErrM

data FunRetType = NotFound | Found Type | Conflict | BadErr String
    deriving (Eq, Ord, Show, Read)

-- the head is current scope, each scope in current state is represented as list element
type TypeCheckerState = [Map Ident Type]
type GetTypeResponse = Err Type
type CheckStatementResponse = Err TypeCheckerState
type CheckFunStatementResponse = Err TypeCheckerState

-- constant strings for messages
type_mismatch = "Type mismatch: "
binary_operation_type_not_allowed = "This type is not allowed in this binary operation"
variable_redefenition = "Variable already was defined: "
variant_empty = "Variant can not be empty: "
variant_def_not_found = "Variant does not have the case for: "
cannot_print_type = "Printing is not supported for the type: "
match_statment_not_var = "Trying to apply match statement to object which is not variant"
match_statement_identifiers_error = "There is error in match identifiers statement"
function_return_conflict = "Function definition has conflict beacause of different return types"
check_fun_type_error = "Error in func type checking"

-- help variables
typeCheckerStartState = [Data.Map.empty]
eqTypes = [Int, Bool, Char]

-- FUNCTIONS

checkType :: Program -> CheckStatementResponse
checkType (Program statements) = checkStatements statements typeCheckerStartState

checkStatements :: [Stm] -> TypeCheckerState -> CheckStatementResponse
checkStatements [] state = Ok state
checkStatements (stm : stmts) state =
    checkStatement stm state >>= \state -> checkStatements stmts state

checkStatement :: Stm -> TypeCheckerState -> CheckStatementResponse
checkStatement stm state = case stm of
    -- TODO LOW in future it should check if variable with the same name was not defined in current head scope
    StmDecl (Decl t identifiers) -> return (newScope : (tail state))
      where
        newScope = foldl insertVar (head state) identifiers
        insertVar scope name = Data.Map.insert name t scope
    StmBlock statements ->
        checkStatements statements (Data.Map.empty : state) >>= \state -> return (tail state)
    StmAss name exp -> getTypeForVariable name state >>= \varType -> getType exp state
        >>= \expType -> compareComplexTypes expType varType >>= \_ -> return state
    StmDictAss identifier exp1 exp2 ->
        getTypeForVariable identifier state >>= \dictType -> case dictType of
            Dict keyType valType -> getType exp1 state >>= \t1 ->
                getType exp2 state
                    >>= \t2 -> compareTypes t1 keyType
                            >>= \_ -> compareTypes t2 valType >>= \_ -> return state
            _ -> Bad $ type_mismatch ++ "Dictionary " ++ (show identifier)
    StmIf exp stm               -> checkBoolExpWithStm exp stm state
    StmIfElse exp stmIf stmElse -> getType exp state >>= \expType ->
        compareTypes expType Bool
            >>= \_ -> checkStatement stmIf state
                    >>= \_ -> checkStatement stmElse state >>= \_ -> return state
    StmWhile exp stm -> checkBoolExpWithStm exp stm state
    StmFor forDeclaration expList stmts -> checkForStatement forDeclaration expList stmts state
    StmFunDef (Ident funName) args stmts -> case (Data.Map.lookup (Ident funName) (head state)) of
        Just _  -> Bad (variable_redefenition ++ funName)
        Nothing -> case stateWithFunction of
            Ok newStateWithFunction ->
                checkFunStatements stmts ((Data.Map.fromList listForMap) : newStateWithFunction)
                    >>= \(_ : res) -> return res
            Bad s -> Bad s
          where
            argTypes          = map (\(Arg t _) -> t) args
            stateWithFunction = case funRetType of
                Found t  -> return $ addFunctionToTypeCheckerState funName t argTypes state
                NotFound -> return $ addFunctionToTypeCheckerState funName Void argTypes state
                _        -> Bad $ function_return_conflict ++ (show funRetType)
            listForMap = map (\(Arg t ident) -> (ident, t)) args
            newState   = addFunctionToTypeCheckerState funName
                                                       Void
                                                       argTypes
                                                       ((Data.Map.fromList listForMap) : state)
            funRetType = getFunRetType stmts newState
    StmMatch exp caseStmts -> checkMatchStatement exp caseStmts state
    StmPrint   exp         -> getType exp state >> return state
    StmStepExp exp         -> getType exp state >>= \t -> return state
    StmPrintS  _           -> return state


addFunctionToTypeCheckerState :: String -> Type -> [Type] -> TypeCheckerState -> TypeCheckerState
addFunctionToTypeCheckerState funName funRetType argTypes state =
    (Data.Map.insert (Ident funName) (Fun funRetType argTypes) (head state)) : (tail state)

checkFunStatements :: [Stm] -> TypeCheckerState -> CheckFunStatementResponse
checkFunStatements [] state = Ok state
checkFunStatements (stm : tail) state =
    checkFunStatement stm state >>= \state -> checkFunStatements tail state

getFunRetType :: [Stm] -> TypeCheckerState -> FunRetType
getFunRetType []              _     = NotFound
getFunRetType (funStm : tail) state = chooseBetterType t1 t2
  where
    t1 = getFunRetTypeForStatement funStm state
    t2 = getFunRetType tail state


chooseBetterType :: FunRetType -> FunRetType -> FunRetType
chooseBetterType t1 t2 = case (t1, t2) of
    (Conflict, _       ) -> Conflict
    (_       , Conflict) -> Conflict
    (BadErr s, _       ) -> BadErr s
    (_       , BadErr s) -> BadErr s
    (NotFound, t       ) -> t
    (t       , NotFound) -> t
    (t       , _       ) -> t

getFunRetTypeForStatement :: Stm -> TypeCheckerState -> FunRetType
getFunRetTypeForStatement stm state = case stm of
    RetStm exp -> case (getType exp state) of
        Ok  t -> Found t
        Bad s -> BadErr $ s ++ (show exp)
    RetVoidStm            -> Found Void
    StmBlock stmts        -> getFunRetType stmts state
    StmIf _ stm           -> getFunRetTypeForStatement stm state
    StmIfElse _ stm1 stm2 -> getFunRetType [stm1, stm2] state
    StmWhile _ stm        -> getFunRetTypeForStatement stm state
    StmFor _ _ stmts      -> getFunRetType stmts state
    StmMatch _ caseStmts ->
        getFunRetType (foldl (\acc (CaseStm _ _ stmts) -> stmts ++ acc) [] caseStmts) state
    _ -> NotFound

checkFunStatement :: Stm -> TypeCheckerState -> Err TypeCheckerState
checkFunStatement funStm state = case getPossibleFunStmts funStm of
    []    -> Ok state
    stmts -> checkFunStatements stmts state

checkBoolExpWithStm :: Exp -> Stm -> TypeCheckerState -> CheckStatementResponse
checkBoolExpWithStm exp stmt state = getType exp state >>= \expType ->
    compareTypes expType Bool >>= \_ -> checkStatement stmt state >>= \state -> return state

checkMatchStatement :: Exp -> [CaseStm] -> TypeCheckerState -> CheckStatementResponse
checkMatchStatement exp caseStmts state = getType exp state >>= \t -> case t of
    Var varDeclarations -> checkCaseStatementsAndVarDeclarations caseStmts varDeclarations state
    _                   -> Bad $ type_mismatch ++ match_statment_not_var

checkCaseStatementsAndVarDeclarations
    :: [CaseStm] -> [VarD] -> TypeCheckerState -> CheckStatementResponse
checkCaseStatementsAndVarDeclarations caseStmts declarations state = if equalIdentifiers
    then checkCaseStatementsAndVarDeclarations (Data.List.sort caseStmts)
                                               (Data.List.sort declarations)
                                               state
    else Bad match_statement_identifiers_error
  where
    identifiersFromStmts        = map (\(CaseStm ident _ _) -> ident) caseStmts
    identifiersFromDeclarations = map (\(VarD ident t) -> ident) declarations
    equalIdentifiers =
        Data.List.sort identifiersFromStmts == Data.List.sort identifiersFromDeclarations
    checkCaseStatementsAndVarDeclarations [] [] state = return state
    checkCaseStatementsAndVarDeclarations ((CaseStm ident variable stmts) : stmTail) ((VarD _ t) : declTail) state
        = checkStatement (StmDecl $ Decl t [variable]) (Data.Map.empty : state) >>= \state ->
            checkStatements stmts state >>= \state ->
                checkCaseStatementsAndVarDeclarations stmTail declTail (tail state)

checkForStatement :: Decl -> Exp -> [Stm] -> TypeCheckerState -> CheckStatementResponse
checkForStatement (Decl tDecl ident) expList stmts state =
    checkStatement (StmDecl (Decl tDecl ident)) (Data.Map.empty : state) >>= \state ->
        getType expList state >>= \t -> compareTypes (List tDecl) t
            >>= \_ -> checkStatements stmts state >>= \state -> return (tail state)

getType :: Exp -> TypeCheckerState -> GetTypeResponse
getType exp state = case exp of
    EIncrR identifier              -> checkUnaryOperation Int identifier state
    EIncr  identifier              -> checkUnaryOperation Int identifier state
    EDecrR identifier              -> checkUnaryOperation Int identifier state
    EDecr  identifier              -> checkUnaryOperation Int identifier state
    EIncrExp identifier exp2       -> checkComplexIntOperation identifier exp2 state
    EDecrExp identifier exp2       -> checkComplexIntOperation identifier exp2 state
    EDivExp  identifier exp2       -> checkComplexIntOperation identifier exp2 state
    EMulrExp identifier exp2       -> checkComplexIntOperation identifier exp2 state
    EModrExp identifier exp2       -> checkComplexIntOperation identifier exp2 state
    EInt  _                        -> return Int
    EChar _                        -> return Char
    EValTrue                       -> return Bool
    EValFalse                      -> return Bool
    EList exps                     -> checkListType exps state >>= \t -> return $ List t
    EVar     identifier exp2       -> getType exp2 state >>= \t -> return (Var [VarD identifier t])
    EFun     args       statements -> checkFunType args statements state
    EFunCall identifier exps       -> checkFunCallType identifier exps state
    EDict dictDeclarations         -> checkDictType dictDeclarations state
    EDictGet identifier keyExp     -> checkDictGetType identifier keyExp state
    ENeg exp2                      -> checkUnaryExpOperation Bool exp2 state
    ENot exp2                      -> checkUnaryExpOperation Bool exp2 state
    EMul exp2 exp3                 -> checkComplexBinaryOperation [Int] Int exp2 exp3 state
    EDiv exp2 exp3                 -> checkComplexBinaryOperation [Int] Int exp2 exp3 state
    EMod exp2 exp3                 -> checkComplexBinaryOperation [Int] Int exp2 exp3 state
    EAdd exp2 exp3                 -> checkComplexBinaryOperation [Int] Int exp2 exp3 state
    ESub exp2 exp3                 -> checkComplexBinaryOperation [Int] Int exp2 exp3 state
    ELTH exp2 exp3                 -> checkComplexBinaryOperation [Int] Bool exp2 exp3 state
    ELE  exp2 exp3                 -> checkComplexBinaryOperation [Int] Bool exp2 exp3 state
    EGTH exp2 exp3                 -> checkComplexBinaryOperation [Int] Bool exp2 exp3 state
    EGE  exp2 exp3                 -> checkComplexBinaryOperation [Int] Bool exp2 exp3 state
    EEQU exp2 exp3                 -> checkComplexBinaryOperation eqTypes Bool exp2 exp3 state
    ENE  exp2 exp3                 -> checkComplexBinaryOperation eqTypes Bool exp2 exp3 state
    EAnd exp2 exp3                 -> checkComplexBinaryOperation [Bool] Bool exp2 exp3 state
    EOr  exp2 exp3                 -> checkComplexBinaryOperation [Bool] Bool exp2 exp3 state
    EVariable identifier           -> getTypeForVariable identifier state
    EVarIs exp2 identifier         -> checkIsVarType exp2 identifier state

checkUnaryOperation :: Type -> Ident -> TypeCheckerState -> GetTypeResponse
checkUnaryOperation allowedType identifier state =
    getType (EVariable identifier) state >>= \t -> compareTypes t allowedType

checkUnaryExpOperation :: Type -> Exp -> TypeCheckerState -> GetTypeResponse
checkUnaryExpOperation allowedType exp state =
    getType exp state >>= \t -> compareTypes t allowedType

checkComplexIntOperation :: Ident -> Exp -> TypeCheckerState -> GetTypeResponse
checkComplexIntOperation identifier exp state = getType (EVariable identifier) state >>= \t ->
    compareTypes t Int >>= \_ -> getType exp state >>= \rightType -> compareTypes Int rightType

checkComplexBinaryOperation :: [Type] -> Type -> Exp -> Exp -> TypeCheckerState -> GetTypeResponse
checkComplexBinaryOperation allowedTypes retType leftExp rightExp state =
    getType leftExp state >>= \leftType -> getType rightExp state
        >>= \rightType -> compareTypes leftType rightType >> return retType

multiCompareComplexTypes :: [Type] -> [Type] -> Err ()
multiCompareComplexTypes []           []           = Ok ()
multiCompareComplexTypes (t1 : tail1) (t2 : tail2) = do
    _ <- compareComplexTypes t1 t2
    multiCompareComplexTypes tail1 tail2
multiCompareComplexTypes _ _ = Bad type_mismatch

compareComplexTypes :: Type -> Type -> Err Type
compareComplexTypes (Var  _ ) (Var  t ) = return (Var t) -- TODO prior LOW - check for the ident
compareComplexTypes (List t1) (List t2) = case (t1, t2) of
    (Void, _   ) -> return (List t2)
    (_   , Void) -> return (List t1)
    (_   , _   ) -> if (t1 == t2) then return (List t1) else Bad type_mismatch
compareComplexTypes t1 t2 = compareTypes t1 t2

compareTypes :: Type -> Type -> Err Type
compareTypes t1 t2 =
    if t1 == t2 then Ok t1 else Bad $ type_mismatch ++ (show t1) ++ " ||| " ++ (show t2)

getTypeForVariable :: Ident -> TypeCheckerState -> Err Type
getTypeForVariable (Ident name) [] = Bad (variable_not_found ++ name)
getTypeForVariable identifier (curScope : nextScopes) =
    case (Data.Map.lookup identifier curScope) of
        Just res -> Ok res
        Nothing  -> getTypeForVariable identifier nextScopes


checkDictGetType :: Ident -> Exp -> TypeCheckerState -> GetTypeResponse
checkDictGetType identifier keyExp state =
    getTypeForVariable identifier state >>= \dictType -> case dictType of
        Dict keyType valType ->
            getType keyExp state >>= \t -> compareTypes t keyType >>= \_ -> return valType
        _ -> Bad $ type_mismatch ++ (show identifier) ++ "is not dictionary"

checkDictType :: [EDictD] -> TypeCheckerState -> GetTypeResponse
checkDictType []                     state = return (Dict Void Void)
checkDictType [EDictD keyExp valExp] state = getType keyExp state
    >>= \keyType -> getType valExp state >>= \valType -> return (Dict keyType valType)
checkDictType ((EDictD keyExp valExp) : tail) state = getType keyExp state >>= \keyType ->
    getType valExp state >>= \valType -> checkDictType tail state >>= \(Dict keyType2 valType2) ->
        compareTypes keyType keyType2
            >>= \_ -> compareTypes valType valType2 >>= \_ -> return (Dict keyType valType)


checkFunType :: [Arg] -> [Stm] -> TypeCheckerState -> GetTypeResponse
checkFunType args stmts state = checkFunStatements stmts newState >>= \_ -> case funRetType of
    Found t  -> return $ Fun t (map (\(Arg t _) -> t) args)
    NotFound -> return $ Fun Void (map (\(Arg t _) -> t) args)
    _        -> Bad check_fun_type_error
  where
    argTypes   = map (\(Arg t _) -> t) args
    listForMap = map (\(Arg t ident) -> (ident, t)) args
    newState   = (Data.Map.fromList listForMap : state)
    funRetType = getFunRetType stmts newState

checkFunCallType :: Ident -> [Exp] -> TypeCheckerState -> GetTypeResponse
checkFunCallType identifier exps state = getTypeForVariable identifier state >>= \funType ->
    case funType of
        Fun returnType argTypes -> getExpTypes exps state
            >>= \argTypes2 -> multiCompareComplexTypes argTypes argTypes2 >> return returnType
        _ -> Bad $ type_mismatch ++ (show identifier) ++ " is not a function"


getExpTypes :: [Exp] -> TypeCheckerState -> Err [Type]
getExpTypes [] state = return []
getExpTypes (exp : tail) state =
    getType exp state >>= \t -> getExpTypes tail state >>= \tailTypes -> return (t : tailTypes)

checkIsVarType :: Exp -> Ident -> TypeCheckerState -> GetTypeResponse
checkIsVarType exp identifier state = getType exp state >>= \t -> case t of
    Var varDeclarations -> if exists
        then return Bool
        else Bad (variant_def_not_found ++ (show identifier))
      where
        exists = foldl (\acc (VarD ident _) -> ident == identifier && acc) False varDeclarations
    _ -> Bad $ type_mismatch ++ "is not a variant"

checkListType :: [Exp] -> TypeCheckerState -> GetTypeResponse
checkListType []            state = return Void
checkListType [exp        ] state = getType exp state >>= \t -> return t
checkListType (hExp : exps) state = getType hExp state
    >>= \hType -> checkListType exps state >>= \tType -> compareTypes hType tType

checkForTheSameElements :: Eq a => [a] -> Bool
checkForTheSameElements []      = True
checkForTheSameElements [_    ] = True
checkForTheSameElements (h : t) = (checkForTheSameElements t) && (head t == h)

-- getIfFound :: FunRetType -> TypeCheckerState -> TypeCheckerState -> TypeCheckerState
-- getIfFound
