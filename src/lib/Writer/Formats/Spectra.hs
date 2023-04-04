-----------------------------------------------------------------------------
-- |
-- Module      :  Writer.Formats.Spectra
-- License     :  MIT (see the LICENSE file)
-- Maintainer  :  Yoav Ben Shimon (yoavbenshimon@gmail.com)
--
-- Translates GR(1) specification to Spectra syntax.
--
-----------------------------------------------------------------------------

module Writer.Formats.Spectra where

-----------------------------------------------------------------------------

import Config

import Data.LTL
import Writer.Eval
import Writer.Error
import Data.Specification

import Detection
import Control.Exception
import qualified Data.Char as Char

-----------------------------------------------------------------------------

-- | Spectra format writer.

writeFormat
  :: Configuration -> Specification -> Either Error String

writeFormat c s =
  case detectGR c s of
    Left v -> case v of
      Left err -> Left err
      Right _  -> errNoGR1 "not in GR(1)" "Spectra"
    Right gr
      | level gr > 1 -> errNoGR1 ("in GR(" ++ show (level gr) ++ ")") "Spectra"
      | otherwise    -> printSpectra gr

  where
    printSpectra gr = do
      let
        es = initEnv gr
        ss = initSys gr
        rs = assertEnv gr
        is = assertSys gr
        (le,ls) = case liveness gr of
          []  -> ([],[])
          x:_ -> x

      (iv,ov) <- signals c s

      return $ "spec " ++ maybe "Translated_Specification" (capitalized .rmPrefix "tmp/" .takeWhile (/= '.') . tail . show) (outputFile c) --extracting output name
        ++ "\n\n"
        ++ unlines (map (\y -> "env boolean " ++ y ++ ";") iv) --inputs (env)
        ++ "\n"
        ++ unlines (map (\y -> "sys boolean " ++ y ++ ";") ov) --outputs (sys)
        ++ (if null es then "" else
            "\n" ++ unlines (map (\y -> "asm ini " ++ prFormula y ++ ";") es)) --initial env
        ++ (if null ss then "" else
             "\n" ++ unlines (map (\y -> "gar ini " ++ prFormula y ++ ";") ss)) --initial sys
        ++ (if null rs then "" else
              "\n" ++ unlines (map (\y -> "asm always " ++ prFormula y ++ ";") rs)) --saftey assumptions (env)
        ++ (if null is then "" else
              "\n" ++ unlines (map (\y -> "gar always " ++ prFormula y ++ ";") is)) --saftey guarantees (sys)
        ++ (if null le then "" else
              "\n" ++ unlines (map (\y -> "asm alwEv " ++ prFormula y ++ ";") le)) --liveness assumptions (env)
        ++ (if null ls then "" else
             "\n" ++ unlines (map (\y -> "gar alwEv " ++ prFormula y ++ ";") ls)) --liveness guarantees (sys)

    prFormula fml = case fml of
      TTrue                 -> "true"
      FFalse                -> "false"
      Atomic x              -> show x
      Not x                 -> "!(" ++ prFormula x ++ ")"
      Next x                -> "next(" ++ prFormula' x ++ ")"
      And []                -> prFormula TTrue
      And [x]               -> prFormula x
      And (x:xr)            -> "(" ++ prFormula x ++ ")" ++
                               concatMap (\y -> " & (" ++ prFormula y ++ ")") xr
      Or []                 -> prFormula FFalse
      Or [x]                -> prFormula x
      Or (x:xr)             -> "(" ++ prFormula x ++ ")" ++
                               concatMap (\y -> " | (" ++ prFormula y ++ ")") xr
      Implies x y           -> "(" ++ prFormula x ++ ") -> (" ++ prFormula y ++ ")"
      Equiv x y             -> "(" ++ prFormula x ++ ") <-> (" ++ prFormula y ++ ")"
      _                     -> assert False undefined


      where prFormula' f = case f of
              TTrue                 -> "true"
              FFalse                -> "false"
              Atomic x              -> show x
              Not x                 -> "!(" ++ prFormula' x ++ ")"
              Next {}               -> assert False undefined
              And []                -> prFormula' TTrue
              And [x]               -> prFormula' x
              And (x:xr)            -> "(" ++ prFormula' x ++ ")" ++
                                       concatMap (\y -> " & (" ++ prFormula' y ++ ")") xr
              Or []                 -> prFormula' FFalse
              Or [x]                -> prFormula' x
              Or (x:xr)             -> "(" ++ prFormula' x ++ ")" ++
                                       concatMap (\y -> " | (" ++ prFormula' y ++ ")") xr
              Implies x y           -> "(" ++ prFormula' x ++ ") -> (" ++ prFormula' y ++ ")"
              Equiv x y             -> "(" ++ prFormula' x ++ ") <-> (" ++ prFormula' y ++ ")"
              _                     -> assert False undefined

rmPrefix :: [Char] -> [Char] -> [Char]
rmPrefix [] ys = ys
rmPrefix _ [] = []
rmPrefix xs ys =
  if xs == take n ys
  then drop n ys
  else ys
  where n = length xs

capitalized :: String -> String
capitalized (head:tail) = Char.toUpper head : tail
capitalized [] = []

-----------------------------------------------------------------------------
