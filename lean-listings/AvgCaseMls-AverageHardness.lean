/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Serialization
import AvgCaseMls.AvCom

/-!
Semantic language of satisfiable MLS formulas (Phase **2D** / S8).

Average-case hardness corollaries live in [AvgCaseMls/NonAvP.lean](#avgcasemls-nonavp-lean) (Phase **5**).
-/

open MLS AvCom

def SatMLS : Set Bitstring :=
  { s | exists (f : Formula), serializeFormula f = s /\ exists (env : Env), evalFormula env f }
