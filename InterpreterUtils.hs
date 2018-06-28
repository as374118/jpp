module InterpreterUtils where

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
import           System.IO                      ( stderr
                                                , stdout
                                                , hPutStrLn
                                                )
import           Control.Monad.State.Lazy

import           AbsVarlang
import           VarlangState
import           ErrM

empty_program = "Program is empty: "
not_implemented = "Not implemented: "
for_error_decl_amount = "There is error in number of declarations in for statement: "
for_statement_not_for_list = "For statement can be applied only to lists: "
key_not_found_in_dict = "Key not found in dict: "
is_not_dict = "Is not a dictionary: "
is_not_variant = "Is not a variant inside match statement: "
not_var_for_is_exp = "Trying to use not a variant in is expression: "
is_not_bool = "Trying to use bool operation on non-bool element: "
is_not_int = "Trying to use int operation for non-int expression: "
error_in_binary_int_evaluation = "Type error in binary int evaluation: "
error_in_binary_bool_evaluation = "Type error in binary bool evaluation: "
error_in_dict_assigning = "Error while trying to assign value to dictionary: "
fun_call_error = "Trying to call object which is not a function: "
divide_by_zero = "Trying to divide by zero: "

interpret :: Program -> MyState
interpret (Program []   ) = Bad empty_program
interpret (Program stmts) = execState (runStatements stmts) startStateVL

runFunStatements :: [Stm] -> State MyState Val
runFunStatements []           = return ValNone
runFunStatements (stm : tail) = do
    case stm of
        RetStm exp -> runExpEvaluation exp
        RetVoidStm -> return ValVoid
        stm        -> do
            val <- runFunStatement stm
            if (val == ValNone) then runFunStatements tail else return val

runFunStatement :: Stm -> State MyState Val
runFunStatement stm = do
    case stm of
        RetVoidStm -> return ValVoid
        RetStm exp -> do
            val <- runExpEvaluation exp
            return val
        _ -> runStatementHelp stm runFunStatement runFunStatements


runStatements :: [Stm] -> State MyState Val
runStatements []           = return ValNone
runStatements (stm : tail) = do
    runStatement stm
    runStatements tail

-- This function takes additional functional params for processing statement wheni tgoes into scopes
runStatementHelp
    :: Stm -> (Stm -> State MyState Val) -> ([Stm] -> State MyState Val) -> State MyState Val
runStatementHelp stm singleStmRunFunction multiStmRunFunction = do
    state <- get
    case state of
        Bad s -> return ValNone
        _ -> case stm of
            StmDecl  (Decl t identifiers) -> declareVariables t identifiers
            StmBlock stmts                -> do
                state <- get
                case state of
                    Bad s                 -> return ValNone
                    Ok  (StateVL env _ _) -> do
                        multiStmRunFunction stmts
                        revertState env
                        return ValNone
            StmAss ident exp -> do
                val <- runExpEvaluation exp
                modify (changeValInState ident val)
                return ValNone
            StmDictAss ident expKey expVal -> do
                valKey <- runExpEvaluation expKey
                valVal <- runExpEvaluation expVal
                runDictAssigning ident valKey valVal
                return ValNone
            StmStepExp exp -> do
                runExpEvaluation exp
                return ValNone
            StmIf exp stm -> do
                valCond <- runExpEvaluation exp
                if (valCond == ValBool True) then singleStmRunFunction stm else return ValNone
            StmIfElse exp stmIf stmElse -> do
                valCond <- runExpEvaluation exp
                if (valCond == ValBool True)
                    then singleStmRunFunction stmIf
                    else singleStmRunFunction stmElse
            StmWhile exp stm -> do
                valCond <- runExpEvaluation exp
                if (valCond == ValBool True)
                    then do
                        val <- singleStmRunFunction stm
                        if (isNone val) then singleStmRunFunction (StmWhile exp stm) else return val
                    else return ValNone
            StmFor (Decl t idents) exp stmts -> if (length idents /= 1)
                then do
                    modify $ addError for_error_decl_amount
                    return ValNone
                else do
                    valList <- runExpEvaluation exp
                    state   <- get
                    case state of
                        Ok (StateVL env _ _) -> do
                            return ()
                            singleStmRunFunction (StmDecl (Decl t idents))
                            if isList valList
                            then
                                runStatementsForVals (head idents)
                                                     (getValList valList)
                                                     stmts
                                                     multiStmRunFunction
                            else
                                do
                                    modify $ addError $ for_statement_not_for_list ++ (show valList)
                                    return ValNone
                        Bad s -> return ValNone
            StmFunDef ident args funStmts -> do
                singleStmRunFunction $ StmDecl $ (Decl (Fun Void [])) [ident]
                singleStmRunFunction (StmAss ident (EFun args funStmts))
            StmMatch exp caseStmts -> do
                val <- runExpEvaluation exp
                case val of
                    ValVar ident valForVar ->
                        let caseStm = find (\(CaseStm ident2 _ _) -> ident == ident2) caseStmts
                        in  case caseStm of
                                Just (CaseStm _ ident stmts) -> do
                                    state <- get
                                    case state of
                                        Ok (StateVL env _ _) -> do
                                            modify (addToState ident valForVar)
                                            val <- multiStmRunFunction stmts
                                            revertState env
                                            return val
                                        Bad s -> return ValNone
                                Nothing -> return ValNone
                    _ -> do
                        modify $ addError is_not_variant
                        return ValNone
            StmPrint exp -> do
                val <- runExpEvaluation exp
                modify (printVal val)
                return ValNone
            StmPrintS str -> do
                modify (printStr str)
                return ValNone

runStatement :: Stm -> State MyState Val
runStatement stm = runStatementHelp stm runStatement runStatements

declareVariables :: Type -> [Ident] -> State MyState Val
declareVariables t identifiers = do
    state <- get
    put $ foldl (\state ident -> addToState ident (getDefaultVal t) state) state identifiers
    return ValNone

runStatementsForVals :: Ident -> [Val] -> [Stm] -> ([Stm] -> State MyState Val) -> State MyState Val
runStatementsForVals _     []           _     _                   = return ValNone
runStatementsForVals ident (val : tail) stmts multiStmRunFunction = do
    modify (changeValInState ident val)
    val <- multiStmRunFunction stmts
    if (isNone val) then runStatementsForVals ident tail stmts multiStmRunFunction else return val


revertState :: Env -> State MyState ()
revertState oldEnv = do
    state <- get
    case state of
        Bad s                          -> return ()
        Ok  (StateVL _ vals lastIndex) -> put $ cleanState (Ok $ StateVL oldEnv vals lastIndex)

runDictAssigning :: Ident -> Val -> Val -> State MyState ()
runDictAssigning ident valKey valVal = do
    valDict <- runExpEvaluation (EVariable ident)
    case valDict of
        ValDict d -> do
            let newDictVal = ValDict (Data.Map.insert valKey valVal d)
            modify $ changeValInState ident newDictVal
        _ -> do
            modify $ addError error_in_dict_assigning

runExpsEvaluation :: [Exp] -> State MyState [Val]
runExpsEvaluation []           = return []
runExpsEvaluation (exp : tail) = do
    val  <- runExpEvaluation exp
    vals <- runExpsEvaluation tail
    return (val : vals)

runExpEvaluation :: Exp -> State MyState Val
runExpEvaluation exp = do
    state <- get
    case state of
        Bad s                           -> return ValVoid
        Ok  (StateVL env vals helpVars) -> case exp of
            EIncrR ident       -> runUnaryIntEvaluation ident (incrIntVal 1) id
            EIncr  ident       -> runUnaryIntEvaluation ident (incrIntVal 1) (incrIntVal 1)
            EDecrR ident       -> runUnaryIntEvaluation ident (decrIntVal 1) id
            EDecr  ident       -> runUnaryIntEvaluation ident (decrIntVal 1) (decrIntVal 1)
            EIncrExp ident exp -> runBinaryIntEvaluation ident exp incrIntVal incrIntVal
            EDecrExp ident exp -> runBinaryIntEvaluation ident exp decrIntVal decrIntVal
            EDivExp  ident exp -> runBinaryIntEvaluation ident exp divIntVal divIntVal
            EMulrExp ident exp -> runBinaryIntEvaluation ident exp multIntVal multIntVal
            EModrExp ident exp -> runBinaryIntEvaluation ident exp modIntVal modIntVal
            EVariable ident    -> do
                state <- get
                let (val, stateNew) = getValFromState ident state
                put stateNew
                return val
            EInt  int  -> return $ ValInt (fromInteger int)
            EChar char -> return $ ValChar char
            EValTrue   -> return $ ValBool True
            EValFalse  -> return $ ValBool False
            EList exps ->
                runExpsEvaluation exps >>= \vals -> return $ ValList (getTypeForVals vals) vals
            EVar ident exp -> do
                val <- runExpEvaluation exp
                return $ ValVar ident val
            EFun args funStmts -> do
                return $ ValFun Void args funStmts
            EFunCall ident exps -> do
                valFun <- runExpEvaluation (EVariable ident)
                case valFun of
                    ValFun _ args funStmts -> do
                        vals  <- runExpsEvaluation exps
                        state <- get
                        case state of
                            Ok (StateVL env _ _) -> do
                                addFunArgsToScope args vals
                                res <- runFunStatements funStmts
                                case res of
                                    ValNone -> return ValVoid
                                    _       -> return res
                            Bad s -> return ValVoid
                    _ -> do
                        modify $ addError $ fun_call_error ++ (show ident)
                        return ValVoid
            EDict dictDeclarations -> do
                dictVals <- runDictDeclEvaluation dictDeclarations
                return $ ValDict $ Data.Map.fromList dictVals
            EDictGet ident exp -> do
                dict <- runExpEvaluation (EVariable ident)
                case dict of
                    ValDict d -> do
                        key <- runExpEvaluation exp
                        case Data.Map.lookup key d of
                            Nothing -> do
                                modify $ addError key_not_found_in_dict
                                return ValVoid
                            Just val -> return val
                    _ -> do
                        modify $ addError is_not_dict
                        return ValVoid
            EVarIs exp ident -> do
                val <- runExpEvaluation exp
                case val of
                    ValVar ident2 val -> return $ ValBool (ident2 == ident)
                    _                 -> do
                        modify $ addError $ not_var_for_is_exp ++ (show exp)
                        return ValVoid
            ENeg exp -> do
                val <- runExpEvaluation exp
                case val of
                    ValInt i -> return $ ValInt (-i)
                    _        -> do
                        modify $ addError $ is_not_int ++ (show val)
                        return ValVoid
            ENot exp -> do
                val <- runExpEvaluation exp
                case val of
                    ValBool p -> return $ ValBool (not p)
                    _         -> do
                        modify $ addError $ is_not_bool ++ (show val)
                        return ValVoid
            EMul exp1 exp2 -> runBinaryIntValEvaluation exp1 exp2 (*)
            EDiv exp1 exp2 -> do
                checkDividingByZero exp2
                state <- get
                case state of
                    Ok _ -> runBinaryIntValEvaluation exp1 exp2 div
                    _ -> return ValNone
            EMod exp1 exp2 -> runBinaryIntValEvaluation exp1 exp2 mod
            EAdd exp1 exp2 -> runBinaryIntValEvaluation exp1 exp2 (+)
            ESub exp1 exp2 -> runBinaryIntValEvaluation exp1 exp2 (-)
            ELTH exp1 exp2 -> runBinaryEvaluation exp1 exp2 (<)
            ELE  exp1 exp2 -> runBinaryEvaluation exp1 exp2 (<=)
            EGTH exp1 exp2 -> runBinaryEvaluation exp1 exp2 (>)
            EGE  exp1 exp2 -> runBinaryEvaluation exp1 exp2 (>=)
            EEQU exp1 exp2 -> runBinaryEvaluation exp1 exp2 (==)
            ENE  exp1 exp2 -> do
                checkDividingByZero exp2
                runBinaryEvaluation exp1 exp2 (/=)
            EAnd exp1 exp2 -> runBinaryBoolValEvaluation exp1 exp2 (&&)
            EOr  exp1 exp2 -> runBinaryBoolValEvaluation exp1 exp2 (||)

checkDividingByZero :: Exp -> State MyState ()
checkDividingByZero exp = do
    val <- runExpEvaluation exp
    if (val == ValInt 0)
        then put (Bad divide_by_zero)
        else return ()

addFunArgsToScope :: [Arg] -> [Val] -> State MyState ()
addFunArgsToScope []                         []               = return ()
addFunArgsToScope ((Arg _ ident) : tailArgs) (val : tailVals) = do
    modify $ addToState ident val
    addFunArgsToScope tailArgs tailVals

runDictDeclEvaluation :: [EDictD] -> State MyState [(Val, Val)]
runDictDeclEvaluation []                              = return []
runDictDeclEvaluation ((EDictD expKey expVal) : tail) = do
    valKey  <- runExpEvaluation expKey
    valVal  <- runExpEvaluation expVal
    tailRes <- runDictDeclEvaluation tail
    return $ (valKey, valVal) : tailRes

runBinaryEvaluation :: Exp -> Exp -> (Val -> Val -> Bool) -> State MyState Val
runBinaryEvaluation exp1 exp2 fun = do
    val1 <- runExpEvaluation exp1
    val2 <- runExpEvaluation exp2
    return $ ValBool (fun val1 val2)

runBinaryBoolValEvaluation :: Exp -> Exp -> (Bool -> Bool -> Bool) -> State MyState Val
runBinaryBoolValEvaluation exp1 exp2 funChange = do
    val1 <- runExpEvaluation exp1
    val2 <- runExpEvaluation exp2
    case (val1, val2) of
        (ValBool p1, ValBool p2) -> return $ ValBool (funChange p1 p2)
        _                        -> do
            modify $ addError $ error_in_binary_bool_evaluation
            return ValVoid

runBinaryIntValEvaluation :: Exp -> Exp -> (Int -> Int -> Int) -> State MyState Val
runBinaryIntValEvaluation exp1 exp2 funChange = do
    val1 <- runExpEvaluation exp1
    val2 <- runExpEvaluation exp2
    case (val1, val2) of
        (ValInt i1, ValInt i2) -> return $ ValInt (funChange i1 i2)
        _                      -> do
            modify $ addError $ error_in_binary_int_evaluation
            return ValVoid


runBinaryIntEvaluation :: Ident -> Exp -> IntValOperation -> IntValOperation -> State MyState Val
runBinaryIntEvaluation ident exp funChange funReturn = do
    (ValInt i ) <- runExpEvaluation (EVariable ident)
    (ValInt i2) <- runExpEvaluation exp
    modify $ changeValInState ident (funChange i2 (ValInt i))
    return (funReturn i2 (ValInt i))

runUnaryIntEvaluation :: Ident -> (Val -> Val) -> (Val -> Val) -> State MyState Val
runUnaryIntEvaluation ident funChange funReturn = do
    (ValInt i) <- runExpEvaluation (EVariable ident)
    modify $ changeValInState ident (funChange (ValInt i))
    return (funReturn (ValInt i))

getFunRetType :: Type -> Type -> Type
getFunRetType t1 t2 = case (t1, t2) of
    (Void, Void) -> Void
    (t   , Void) -> t
    (Void, t   ) -> t
    (t1  , _   ) -> t1


