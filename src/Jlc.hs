module Main where
    
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess,exitWith, ExitCode(..))
import System.Cmd (system)
import System.FilePath.Posix (dropExtension, dropFileName)
import System.IO (stderr, hPutStrLn)
import Javalette.Abs
import Javalette.Lex
import Javalette.Par
import Javalette.ErrM
import Javalette.Print
   
import Frontend.TypeChecker
import qualified Backend.CodeGenLLVM as LLVM

import Control.Monad
    
debug :: Bool
debug = True

printErr :: String -> IO ()
printErr = hPutStrLn stderr
                

main :: IO ()
main = do
  args <- getArgs
  case args of
    [backend,file] ->
        do
          when (backend `notElem` ["-llvm"])
                   (do putStrLn "Usage: jlc (-llvm) <SourceFile>"
                       exitFailure)
                   
          let name = dropExtension file
              dir  = dropFileName file
          s <- readFile file
          case pProgram (myLexer s) of
            Bad err  ->
              do
                printErr "ERROR"
                printErr $ "SYNTAX ERROR: " ++ err
                exitFailure
            Ok  tree ->
              case typecheck tree of
                Bad err ->
                  do
                    printErr "ERROR"
                    printErr $ "TYPE ERROR: " ++ err
                    exitFailure
                Ok (str,program) -> 
                  do                  
                    printErr "OK"
                    when debug  (printErr (printTree program))
                    when debug  (printErr (show str         ))
                    case backend of
                      "-llvm" ->
                        case LLVM.genCode name (str,program) of
                          Bad err ->
                            do
                              printErr "ERROR"
                              printErr "COMPILER ERROR"
                              printErr err
                              exitFailure
                          Ok code ->
                            do
                              when debug (printErr code)
                              writeFile (name ++ ".ll") code
                              out <- system $ concat [ "llvm-as "
                                                     , name
                                                     , ".ll"]
                              exitSuccess
      
                      other -> do putStrLn $ "Backend not implemented " ++ tail other
                                  exitFailure
    _      -> do putStrLn "Usage: jlc (-jvm | -llvm) <SourceFile>"
                 exitFailure


