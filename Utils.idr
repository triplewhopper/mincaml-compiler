module Utils

import PrimIO
import System
import System.File
import System.File.Virtual
import Data.Fuel
import Text.Lexer 

public export
red: String -> String
red str = "\x1b[91m\{str}\x1b[0m"

public export
bold: String -> String
bold str = "\x1b[1m\{str}\x1b[0m"

public export
italics: String -> String
italics str = "\x1b[3m\{str}\x1b[0m"

public export
orange: String -> String
orange str = "\x1b[38;5;208m\{str}\x1b[0m"

export
info : (msg : String) -> (result : a) -> a
info x val = unsafePerformIO (do 
    fPutStrLn stderr ("[info] \{x}") >>= (\err => case err of 
        Left err => (putStrLn $ show err) >> exitFailure
        Right () => pure ())
    pure val)

export 
warn : (msg : String) -> (result : a) -> a
warn x val = unsafePerformIO (do 
    fPutStrLn stderr (orange "[warning]" ++ " " ++ x) >>= (\err => case err of 
        Left err => (putStrLn $ show err) >> exitFailure
        Right () => pure ())
    pure val)

export 
eprintLn: (msg : String) -> IO ()
eprintLn x = do 
    fPutStrLn stderr x >>= (\err => case err of 
        Left err => (putStrLn $ show err) >> exitFailure
        Right () => pure ())
    pure ()

export 
failwith : (msg : String) -> a
failwith x = unsafePerformIO (do 
    eprintLn x 
    exitFailure)

export
data FileTooBig = OhFileTooBig

export
Show FileTooBig where
    show OhFileTooBig = "File too big"

export
fromFile : (path : String) -> IO (Either FileError (Either FileTooBig String))
fromFile path = do 
    case !(readFilePage 0 (limit 10485760) path) of 
        Left err => pure (Left err)
        Right (True, strs) => pure (Right (Right (fastConcat strs)))
        Right (False, strs) => pure (Right (Left OhFileTooBig))

export
[a2] Show Bounds where 
    show (MkBounds ln0 cl0 ln1 cl1) = 
        if ln0 == ln1 then """
        line \{show (ln0+1)}, characters \{show (cl0+1)}-\{show (cl1+1)}
        """
        else "line \{show (ln0+1)}-\{show (ln1+1)}, characters \{show (cl0+1)}-\{show (cl1+1)}"

