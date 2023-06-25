{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module LSP.Handlers where

import Language.LSP.Server
import Language.LSP.Types
import Control.Monad.IO.Class
import qualified Data.Text as T
import Compiler.Scanner (scan)
import LSP.Util


import Control.Applicative              ((<|>))
import Control.Lens                     (assign, modifying, use, (^.))
import Control.Monad                    (forM, guard)
import Control.Monad.Trans              (lift, liftIO)
import Control.Monad.Trans.Except       (catchE, throwE, ExceptT, catchE, throwE)
import Data.Aeson                       (FromJSON(..), Value(..))
import Data.Maybe                       (maybeToList, fromMaybe, fromJust)
import Data.Text                        (Text, isPrefixOf)
import qualified Data.Text.IO  as Text
import Language.LSP.Server              (Handlers, LspT)
import Language.LSP.Types               hiding (Range(..), line)
import Language.LSP.Types.Lens hiding (publishDiagnostics)
import Language.LSP.Diagnostics
import System.FilePath
import Language.LSP.VFS (VirtualFile(..))
import qualified Data.Text.Utf16.Rope as Rope
import LSP.State ( ServerConfig, Severity(Error), HandlerM, ast, typedAST, errs )
import Compiler.Parser (parse)
import Compiler.AST (prettyPrintAST, getPrettyPrintedPosition, AST (AST))
import qualified Compiler.Position
import Compiler.Graph (createGraph, buildRootOrder)
import Compiler.Unification (runUnifyEntireAST)
import qualified Compiler.TypedAST as TypedAST
import System.IO (stderr)
import qualified Language.LSP.Types as J
import qualified Language.LSP.Types.Lens as J
import qualified Compiler.Token

diagnosticSourcePrefix :: Text
diagnosticSourcePrefix = "spl-lsp"

debug :: (MonadIO m) => Text -> m ()
debug msg = liftIO $ Text.hPutStrLn stderr $ "[spl-lsp] " <> msg

makeParseErrorDiagnostic :: (Language.LSP.Types.Range, Text) -> Language.LSP.Types.Diagnostic
makeParseErrorDiagnostic (range, msg) =
    Language.LSP.Types.Diagnostic
      range
      (Just Language.LSP.Types.DsError) -- severity
      Nothing -- code
      (Just diagnosticSourcePrefix) -- source
      msg
      Nothing -- tags
      (Just (Language.LSP.Types.List []))

liftLSP :: LspT ServerConfig IO a -> HandlerM a
liftLSP m = lift (lift m)

-- | A helper function to query haskell-lsp's VFS.
readUri :: Uri -> HandlerM Text
readUri uri_ = do
  mVirtualFile <- liftLSP (getVirtualFile (toNormalizedUri uri_))
  case mVirtualFile of
    Just (VirtualFile _ _ rope) -> return (Rope.toText rope)
    Nothing -> throwE (Error, "Could not find " <> T.pack (show uri_) <> " in VFS.")

--scan :: String -> ([PositionedToken], [LexerError])
validateCode :: NormalizedUri -> TextDocumentVersion -> HandlerM ()
validateCode uri version = do
  assign errs []

  txt <- readUri (fromNormalizedUri uri)

  let (tokens, errs') = scan (T.unpack txt)
  let lexErrData = map lexErrDataDiag errs'
  modifying errs (<> lexErrData)

  let (astRes, astErrs') = parse tokens
  let parseErrData = map parseErrDataDiag astErrs'
  modifying errs (<> parseErrData)

  lift $ lift $ flushDiagnosticsBySource 0 (Just diagnosticSourcePrefix)

  ast' <- case astRes of
    Nothing -> do
      errs' <- use errs
      publishDiags $ map makeParseErrorDiagnostic errs'
      throwE (Error, "Failed to parse SPL file.")
    Just ast' -> do
      assign ast astRes
      return ast'

  let (graph, graphErr) = createGraph ast'
  case graph of
    Nothing -> do
      errs' <- use errs
      publishDiags $ map makeParseErrorDiagnostic errs'
      throwE (Error, "Failed to create graph.")
    Just graph' -> do
      let rootOrder = buildRootOrder (fromJust graph) ast'
      let (typeRes, typeErrs') = runUnifyEntireAST (AST rootOrder)

      let typeErrData = map typeErrDataDiag typeErrs'

      modifying errs (<> typeErrData)

      errs' <- use errs
      publishDiags $ map makeParseErrorDiagnostic errs'

      assign typedAST typeRes
  return ()
  where
    publishDiags :: [Diagnostic] -> HandlerM ()
    publishDiags diags = do
      let partitioned = partitionBySource diags
      lift $ lift $ publishDiagnostics 1 uri version partitioned

simpleHandlers :: Handlers HandlerM
simpleHandlers = mconcat
    [ notificationHandler J.SInitialized $ \_not -> do
        debug "Initialized"
    , notificationHandler J.STextDocumentDidSave $ \msg -> do
        let doc = msg ^. J.params . J.textDocument . J.uri
        validateCode (J.toNormalizedUri doc) Nothing
    , notificationHandler J.STextDocumentDidOpen $ \msg -> do
        let doc = msg ^. J.params . J.textDocument . J.uri
        validateCode (J.toNormalizedUri doc) Nothing
    ]

hoverHandler :: Handlers HandlerM
hoverHandler = requestHandler STextDocumentHover $ \req responder -> do
  let RequestMessage _ _ _ (HoverParams _doc pos _workDone) = req
  let Position _l _c = pos

  ast' <- use ast
  typeRes <- use typedAST

  {- TODO 
    Make the pretty printer actually be pretty.
    Vars should only print the type in the typed pretty printer.
  -}
  pretty <- case typeRes of
    Nothing -> case ast' of
      Nothing -> return Nothing
      Just ast -> return $ getPrettyPrintedPosition ast (convertPosition pos)
    Just ta -> return $ TypedAST.getPrettyPrintedPosition ta (convertPosition pos)

  errs''' <- use errs
  case pretty of
    Nothing -> responder (Right Nothing)
    Just s -> do
      let ms = HoverContents $ markedUpContent "lsp" (T.pack (s ++ concatMap (T.unpack . snd) errs'''))
      let range = Range pos pos

      let rsp = Hover ms (Just range)
      responder (Right $ Just rsp)

convertPosition :: Language.LSP.Types.Position -> Compiler.Position.Position
convertPosition (Language.LSP.Types.Position l c) = Compiler.Position.Position (fromIntegral l + 1) (fromIntegral c + 1)

convertPosition' :: Compiler.Position.Position -> Language.LSP.Types.Position
convertPosition' (Compiler.Position.Position l c) = Language.LSP.Types.Position (fromIntegral l -1) (fromIntegral c -1)