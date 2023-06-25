{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}
module LSP.Server where

import Language.LSP.Server
import Language.LSP.Types
import Control.Monad.IO.Class
import qualified Data.Text as T


import LSP.Handlers (hoverHandler, simpleHandlers)
import qualified Control.Concurrent.MVar as MVar
import qualified Data.Aeson as Aeson
import qualified Data.Text as Text
import LSP.State (HandlerM, Severity (..), initialState)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Control.Monad.Trans.Except as Except
import qualified System.Exit as Exit
import System.Exit (ExitCode(..))
import Data.Default (Default(..))
import Data.Aeson (fromJSON)

-- | The main entry point for the LSP server.
run :: IO ()
run = do
  state <- MVar.newMVar initialState

  let defaultConfig = def

  let onConfigurationChange _oldConfig json =
        case fromJSON json of
            Aeson.Success config -> Right config
            Aeson.Error   string -> Left (Text.pack string)

  let doInitialize environment _request = do
          return (Right environment)

  let options = def
        { textDocumentSync = Just syncOptions
        -- , completionTriggerCharacters = Just [':', '.', '/']
        }

  let staticHandlers = mconcat
        [ hoverHandler
        , simpleHandlers
        ]

  let interpretHandler environment = Iso{..}
        where
          forward :: HandlerM a -> IO a
          forward handler =
            MVar.modifyMVar state \oldState -> do
              runLspT environment do
                (e, newState) <- State.runStateT (Except.runExceptT handler) oldState
                result <- case e of
                  Left (Log, _message) -> do
                    let _xtype = MtLog

                    sendNotification SWindowLogMessage LogMessageParams{..}

                    liftIO (fail (Text.unpack _message))

                  Left (severity_, _message) -> do
                    let _xtype = case severity_ of
                          Error   -> MtError
                          Warning -> MtWarning
                          Info    -> MtInfo
                          Log     -> MtLog

                    sendNotification SWindowShowMessage ShowMessageParams{..}
                    liftIO (fail (Text.unpack _message))
                  Right a -> do
                      return a

                return (newState, result)

          backward = liftIO

  exitCode <- runServer ServerDefinition{..}

  case exitCode of
      0 -> return ()
      n -> Exit.exitWith (ExitFailure n)

syncOptions :: TextDocumentSyncOptions
syncOptions = TextDocumentSyncOptions
  { _openClose         = Just True
  , _change            = Just TdSyncIncremental
  , _willSave          = Just False
  , _willSaveWaitUntil = Just False
  , _save              = Just (InR (SaveOptions (Just False)))
  }