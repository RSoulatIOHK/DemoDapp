{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}


module PlutusExample.PlutusVersion2.StakeScript
  ( v2StakeScript
  , v2StakeScriptShortBs
  ) where

import Prelude hiding (($))

import Cardano.Api.Shelley (PlutusScript (..), PlutusScriptV2)
import Prelude hiding (($), (&&))

import Codec.Serialise
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as SBS

import Plutus.Script.Utils.V2.Typed.Scripts.StakeValidators as V2
import Plutus.V2.Ledger.Api qualified as V2
import Plutus.V2.Ledger.Contexts as V2
import PlutusTx qualified
import PlutusTx.Builtins
import PlutusTx.Prelude hiding (Semigroup (..), unless, (.))

{- HLINT ignore "Avoid lambda" -}

{-# INLINABLE mkPolicy #-}
mkPolicy :: BuiltinData -> V2.ScriptContext -> Bool
mkPolicy _redeemer _ctx = True

policy :: V2.StakeValidator
policy = V2.mkStakeValidatorScript $$(PlutusTx.compile [|| wrap ||])
 where
  wrap = V2.mkUntypedStakeValidator mkPolicy

plutusScript :: V2.Script
plutusScript =
  V2.unStakeValidatorScript policy

validator :: V2.Validator
validator = V2.Validator plutusScript

scriptAsCbor :: LBS.ByteString
scriptAsCbor = serialise validator

v2StakeScript :: PlutusScript PlutusScriptV2
v2StakeScript = PlutusScriptSerialised . SBS.toShort $ LBS.toStrict scriptAsCbor

v2StakeScriptShortBs :: SBS.ShortByteString
v2StakeScriptShortBs = SBS.toShort . LBS.toStrict $ scriptAsCbor
