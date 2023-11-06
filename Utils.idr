module Utils

import PrimIO
import System
import System.File
import System.File.Virtual
import Data.Fuel

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
    fPutStrLn stderr ("[warning] \{x}") >>= (\err => case err of 
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