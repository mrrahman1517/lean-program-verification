--Stirling's Approximation Test

--This file demonstrates how to use Mathlib's Stirling approximation for factorials in Lean.
--It evaluates the approximation for n = 10 and compares it to the actual value and to \(\sqrt{\pi}\).


import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
open Stirling

-- Test Stirling's approximation for n = 10
--eval stirlingSeq 10  -- This should be close to Real.sqrt Real.pi

-- Compare with the actual value of 10!
--eval (10.factorial : ℝ) / (Real.sqrt (2 * 10) * (10 / Real.exp 1) ^ 10)

-- The value should be close to Real.sqrt Real.pi
--eval Real.sqrt Real.pi
