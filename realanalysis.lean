import Mathlib.Data.Real.Basic

-- Boyle's Law Theorem

--This file contains a formalization and proof of Boyle's Law from physics:
--If the temperature and amount of gas are constant, then the product of pressure and volume is constant.


theorem Boyle {P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ}

(h1 : P1 * V1 = n1 * R * T1)
(h2 : P2 * V2 = n2 * R * T2)
(h3 : T1 = T2)
(h4 : n1 = n2) :
P1 * V1 = P2 * V2 :=

by
rw [h3] at h1
rw [h4] at h1
rw [← h2] at h1
exact h1
