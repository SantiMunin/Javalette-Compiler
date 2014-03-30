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
-- import qualified Backend.CodeGenJVM as JVM
-- import qualified Backend.CodeGenLLVM as LLVM

import Control.Monad
    
debug :: Bool
debug = True

printErr :: String -> IO ()
printErr = hPutStrLn stderr
                
frontend :: String -> String -> Err Program 
frontend name s = case pProgram (myLexer s) of
            Bad err  -> fail $ "SYNTAX ERROR: " ++ err
            Ok  tree -> case typecheck tree of
                          Bad err -> fail $ "TYPE ERROR: " ++ err
                          Ok tree' -> return tree'
                                     
main :: IO ()
main = do
  args <- getArgs
  case args of
    [backend,file] ->
        do
          when (backend `notElem` ["-jvm", "-llvm"])
                   (do putStrLn "Usage: jlc (-jvm | -llvm) <SourceFile>"
                       exitFailure)
                   
          let name = dropExtension file
              dir  = dropFileName file
          s <- readFile file
          case frontend name s of
            Bad err -> printErr "ERROR" >> printErr err >> exitFailure
            Ok tree -> do
              printErr "OK"
              when debug  (printErr (printTree tree))
{-              case backend of
     --           "-jvm"  -> compile JVM.genCode  successJVM
                "-llvm" -> compile LLVM.genCode successLLVM
              where
                compile generator success = do
                  case generator name tree of
                    Bad err -> do
                      printErr "ERROR" >> printErr "COMPILER ERROR"
                      printErr err
                      exitFailure
                    Ok code -> success code

  {- If -jvm
                successJVM :: String -> IO ()
                successJVM code = do
                  writeFile (name ++ ".j") code 
                  out <- system $ concat [ "java -jar lib/jasmin.jar -d "
                                         , dir
                                         , " "
                                         , name
                                         , ".j"]
                  showResult (printErr (printTree tree))  out name "jvm" ".class" 
                  exitSuccess
  -} -- If -llvm
                successLLVM :: String -> IO ()
                successLLVM code = do
                  writeFile (name ++ ".ll") code
                  out <- system $ concat [ "llvm-as "
                                         , name
                                         , ".ll"]
                  showResult (printErr (printTree tree) >> printErr code) out  name "llvm" ".ll"
                  exitSuccess
      
                
    _      -> do putStrLn "Usage: jlc (-jvm | -llvm) <SourceFile>"
                 exitFailure

showResult :: IO () -> ExitCode -> String -> String -> String -> IO ()
showResult debugP ExitSuccess name msg ext = do
  printErr "OK"
  when debug debugP
  printErr $ "Code generated for " ++ msg ++ " : " ++ name ++ ext
showResult _ (ExitFailure _) _ _ _ = exitFailure
-}
