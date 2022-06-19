import Control.MonadReader.ReaderT
import Control.MonadReader.MonadTrans

-- Demo used in Result section of the paper

data Vault = Vault
  { password :: String
  , content :: String
  }

hide_vault_content :: Vault -> Vault
hide_vault_content (Vault p c) = (Vault p "nothing")

openVault :: ReaderT Vault IO ()
openVault = do
    given_password <- lift $ getLine 
    actual_password <- asksT (password)
    if (given_password /= actual_password)
      then do
        vault_content <- localT (hide_vault_content) (asksT (content))
        lift $ putStrLn ("You get: " ++ vault_content)
      else do 
        vault_content <- asksT (content)
        lift $ putStrLn ("You get: " ++ vault_content)

main :: IO ()
main = runReaderT openVault (Vault "secretPassword" "diamonds")