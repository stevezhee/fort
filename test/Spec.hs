import Parser
import System.FilePath
import System.Directory

main :: IO ()
main = do
  files <- filter (isExtensionOf ".fort") <$> listDirectory "test"
  mapM_ parseAndCodeGen $ map ("test" </>) files
  putStrLn "test Spec.hs complete"

isExtensionOf :: String -> FilePath -> Bool
isExtensionOf ext = (==) ext . takeExtension
