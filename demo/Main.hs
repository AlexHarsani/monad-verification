import Data.MonadReader.Reader
import Data.MonadReader.ReaderT
import Data.MonadReader.MonadTrans


data User = User
  { userName :: String
  , userPassword :: String
  }


checkPassword :: String -> Reader User Bool
checkPassword p = do
  actualP <- asks (userPassword)
  return (p == actualP)


{-
welcomeMessage :: Reader User String
welcomeMessage = do
  user <- ask
  return ("Welcome " ++ (userName user) ++ "!")


checkPasswordAndWelcome :: User -> String -> Maybe String
checkPasswordAndWelcome u p =
  if runReader (checkPassword p) u
  then Just (runReader welcomeMessage u)
  else Nothing
-}

-- main :: IO ()
-- main = print $ (checkPasswordAndWelcome (User "Alex" "aaa") "aaa")


printReaderContent :: ReaderT String IO ()
printReaderContent = do
    content <- askT
    name <- liftM $ getLine 
    liftM $ putStrLn ("The Message of the Day: " ++ content ++ name)

main :: IO ()
main = runReaderT printReaderContent "Hello, "

