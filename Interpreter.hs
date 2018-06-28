module Main where

import           System.Environment             ( getArgs )
import           System.IO                      ( stderr
                                                , stdout
                                                , hPutStrLn
                                                , hPutStr
                                                )
import           Data.Map                       ( Map
                                                , insert
                                                , lookup
                                                , size
                                                , fromList
                                                , empty
                                                , showTree
                                                )
import           Control.Monad                  ( liftM
                                                , liftM2
                                                , liftM3
                                                , join
                                                )

import           AbsVarlang
import           ParVarlang
import           LexVarlang
import           ErrM

import           TypeChecker
import           VarlangState
import           InterpreterUtils

debug_param = "--DEBUG"
type_checked = "Type was successfully checked. The main scope is: "
program_finished = "Program finished successfully: "
files_not_passed = "Please pass filenames in arguments: "
program_error = "Program error: "

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> hPutStrLn stderr files_not_passed
        _ ->
            let checker (isDebug, names) s =
                    if (s == debug_param) then (True, names) else (isDebug, s : names)
                (isDebug, names) = foldl checker (False, []) args
            in  mapM_ (\f -> readFile f >>= calc isDebug) names

calc :: Bool -> String -> IO ()
calc isDebug s = case pProgram $ myLexer s of
    Bad s    -> hPutStrLn stderr s
    Ok  tree -> case checkType tree of
        Bad s -> hPutStrLn stderr s
        Ok st ->
            printDebug isDebug (type_checked ++ (show st))
                >> printDebug isDebug "Interpreting started"
                >> case (interpret tree) of
                       Bad s -> hPutStrLn stderr (program_error ++ s)
                       Ok (StateVL _ _ (HelpVars _ strsToPrint)) -> do
                           mapM_ (hPutStr stdout) (reverse strsToPrint)
                           printDebug isDebug
                                      (program_finished ++ " | current state: " ++ (show st))


printDebug :: Bool -> String -> IO ()
printDebug isDebug str = hPutStrLn stdout (if isDebug then str else "")
