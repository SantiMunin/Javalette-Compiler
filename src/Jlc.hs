module Main where

import           Javalette.Abs
import           Javalette.ErrM
import           Javalette.Lex
import           Javalette.Par
import           Javalette.Print
import           System.Cmd            (system)
import           System.Environment    (getArgs)
import           System.Exit           (ExitCode (..), exitFailure, exitSuccess,
                                        exitWith)
import           System.FilePath.Posix (dropExtension, dropFileName)
import           System.IO             (hPutStrLn, stderr)

import           Backend.CodeGenLLVM
import           Frontend.Desugar
import           Frontend.TypeCheck

import           Control.Monad

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
              case desugar tree of
                Bad err ->
                  do
                    printErr "ERROR"
                    printErr $ "DESUGAR ERROR: " ++ err
                    exitFailure
                Ok (str, classes, fnDefs) -> do
                  case typecheck (str, classes, fnDefs) of
                    Bad err ->
                      do
                        printErr "ERROR"
                        printErr $ "TYPE ERROR: " ++ err
                        when debug  (printErr (printTree fnDefs))
                        when debug  (printErr (show str        ))
                        exitFailure
                    Ok (str, classes, typedFnDefs) ->
                      do
                        printErr "OK"
                        when debug  (printErr (printTree typedFnDefs))
                        when debug  (printErr (show str         ))
                        case backend of
                          "-llvm" ->
                            case genCode (str, classes, typedFnDefs) of
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

                          other ->
                            do
                              putStrLn $
                                     "Backend not implemented " ++ tail other
                              exitFailure
    _      -> do putStrLn "Usage: jlc (-jvm | -llvm) <SourceFile>"
                 exitFailure


