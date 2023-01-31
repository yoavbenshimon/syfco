-----------------------------------------------------------------------------
-- |
-- Module      :  Writer.Formats.SpectraSpot
-- License     :  MIT (see the LICENSE file)
-- Maintainer  :  Yoav Ben Shimon (yoavbenshimon@gmail.com)
--
-- Translates GR(1) specification to Spectra via Spot:
-- Generates an intermidiery format readable by an external script which attempts
-- to covert each assumption\guaranteeto GR(1) in a sound and complete procedure
--
-----------------------------------------------------------------------------

module Writer.Formats.SpectraSpot where

-----------------------------------------------------------------------------

import Config

import Data.LTL
import Writer.Eval
import Writer.Error
import Data.Specification
import Control.Exception

-----------------------------------------------------------------------------

-- | Spectra format writer.

writeFormat
  :: Configuration -> Specification -> Either Error String

writeFormat c s = do
    (es,ss,rs,as,is,gs) <- eval c s
    (iv,ov) <- signals c s
    let asm = es ++ map fGlobally rs ++ as
    let gar = ss ++ map fGlobally is ++ gs

    return $ "spec " ++ maybe "Translated_Specification" (takeWhile (/= '.') . tail . show) (outputFile c) --extracting output name
      ++ "\n\n"
      ++ unlines (map (\y -> "env boolean " ++ y ++ ";") iv) --inputs (env)
      ++ "\n"
      ++ unlines (map (\y -> "sys boolean " ++ y ++ ";") ov) --outputs (sys)
      ++ (if null asm then "" else
          "\n" ++ unlines (map (\y -> "asm " ++ prFormula y ++ ";") asm)) --assumptions
      ++ (if null gar then "" else
           "\n" ++ unlines (map (\y -> "gar " ++ prFormula y ++ ";") gar)) --guarantees

    where
      prFormula fml = case fml of
        TTrue                 -> "true"
        FFalse                -> "false"
        Atomic x              -> show x
        Not x                 -> "!(" ++ prFormula x ++ ")"
        Implies x y           -> "(" ++ prFormula x ++ ") -> (" ++ prFormula y ++ ")"
        Equiv x y             -> "(" ++ prFormula x ++ ") <-> (" ++ prFormula y ++ ")"
        Next x                -> "next(" ++ prFormula' x ++ ")"
        Globally x            -> "G(" ++ prFormula x ++ ")"
        Finally x             -> "F(" ++ prFormula x ++ ")"
        Until x y             -> "(" ++ prFormula x ++ ") U (" ++ prFormula y ++ ")"
        Release x y           -> "(" ++ prFormula x ++ ") R (" ++ prFormula y ++ ")"
        Weak x y              -> "(" ++ prFormula x ++ ") W (" ++ prFormula y ++ ")"
        And []                -> prFormula TTrue
        And [x]               -> prFormula x
        And (x:xr)            -> "(" ++ prFormula x ++ ")" ++
                                 concatMap (\y -> " & (" ++ prFormula y ++ ")") xr
        Or []                 -> prFormula FFalse
        Or [x]                -> prFormula x
        Or (x:xr)             -> "(" ++ prFormula x ++ ")" ++
                                 concatMap (\y -> " | (" ++ prFormula y ++ ")") xr
        _                     -> assert False undefined

        where
          prFormula' fml = case fml of
            TTrue                 -> "true"
            FFalse                -> "false"
            Atomic x              -> show x
            Not x                 -> "!(" ++ prFormula' x ++ ")"
            Implies x y           -> "(" ++ prFormula' x ++ ") -> (" ++ prFormula' y ++ ")"
            Equiv x y             -> "(" ++ prFormula' x ++ ") <-> (" ++ prFormula' y ++ ")"
            Next x                -> "X(" ++ prFormula' x ++ ")" -- this is written differently to help detect nested next without erroring
            Globally x            -> "G(" ++ prFormula' x ++ ")"
            Finally x             -> "F(" ++ prFormula' x ++ ")"
            Until x y             -> "(" ++ prFormula' x ++ ") U (" ++ prFormula' y ++ ")"
            Release x y           -> "(" ++ prFormula' x ++ ") R (" ++ prFormula' y ++ ")"
            Weak x y              -> "(" ++ prFormula' x ++ ") W (" ++ prFormula' y ++ ")"
            And []                -> prFormula' TTrue
            And [x]               -> prFormula' x
            And (x:xr)            -> "(" ++ prFormula' x ++ ")" ++
                                 concatMap (\y -> " & (" ++ prFormula' y ++ ")") xr
            Or []                 -> prFormula' FFalse
            Or [x]                -> prFormula' x
            Or (x:xr)             -> "(" ++ prFormula' x ++ ")" ++
                                 concatMap (\y -> " | (" ++ prFormula' y ++ ")") xr
            _                     -> assert False undefined


-----------------------------------------------------------------------------
