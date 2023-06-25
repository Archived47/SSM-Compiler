{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module LSP.State where

import Control.Lens.TH                  (makeLenses)
import Control.Monad.Trans.Except       (ExceptT)
import Control.Monad.Trans.State.Strict (StateT)
import Data.Aeson
    ( FromJSON (..)
    , withObject
    , (.!=)
    , (.:)
    , (.:?)
    )
import Data.Default                     (Default (def))
import Data.Dynamic                     (Dynamic)
import Data.Map.Strict                  (Map, empty)
import Data.Text                        (Text)
import Language.LSP.Server              (LspT)


import Data.Aeson.Key (fromString)
import qualified Data.Map as Map
import Control.Lens (use)
import qualified Compiler.AST as AST
import qualified Compiler.Parser as AST
import qualified Compiler.TypedAST as TAST
import qualified Compiler.Unification as TAST
import Language.LSP.Types (Range)


-- Inside a handler we have access to the ServerState. The exception layer
-- allows us to fail gracefully, displaying a message to the user via the
-- "ShowMessage" mechanism of the lsp standard.
type HandlerM = ExceptT (Severity, Text) (StateT ServerState (LspT ServerConfig IO))

data Severity = Error
              -- ^ Error displayed to the user.
              | Warning
              -- ^ Warning displayed to the user.
              | Info
              -- ^ Information displayed to the user.
              | Log
              -- ^ Log message, not displayed by default.

data ServerConfig = ServerConfig { } deriving Show

instance Default ServerConfig where
  def = ServerConfig { }

-- We need to derive the FromJSON instance manually in order to provide defaults
-- for absent fields.
instance FromJSON ServerConfig where
  parseJSON = withObject "settings" $ \v -> do
    v .: fromString "vscode-dhall-lsp-server"


data ServerState = ServerState { _ast :: Maybe AST.AST, _typedAST :: Maybe TAST.TypedAST, _errs :: [(Range, Text)] }

makeLenses ''ServerState

initialState :: ServerState
initialState = ServerState { _ast = Nothing, _typedAST = Nothing, _errs = [] }
