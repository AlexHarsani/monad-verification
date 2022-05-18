import Data.MonadReader.MyReader

data User = User
  { userName :: String
  , userPassword :: String
  }

checkPassword :: String -> MyReader User Bool
checkPassword p = do
  actualP <- asks (userPassword)
  return (p == actualP)

welcomeMessage :: MyReader User String
welcomeMessage = do
  user <- ask
  return ("Welcome " ++ (userName user) ++ "!")

checkPasswordAndWelcome :: User -> String -> Maybe String
checkPasswordAndWelcome u p =
  if runReader (checkPassword p) u
  then Just (runReader welcomeMessage u)
  else Nothing

main :: IO ()
main = print $ (checkPasswordAndWelcome (User "Alex" "aaa") "aaa")
