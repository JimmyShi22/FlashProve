-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksRespBank.lean: `Resp.K` (OnBytes/Flat/LinksRespBase.lean) of routines of the
head's check, by the walk of OnBytes/Flat/LinksRespTool.lean.

Each theorem has the name `OnBytes.Flat.RespOf` ++ f of a routine f and says: at all arguments, f
gives the same from two states that are alike. Each is shown by the walk (`resp`), which finds the
theorems on the routines that f calls by their names: so a routine's theorem stands behind those of
the routines that it calls. The statements were written out by a program from the list that the
command `resp_bank` of that file makes; Lean checks each as it stands here. The sections: the
lookup's own claims, seven groups of the head's claims, the merge's claim, and two groups of the
smallness test's claims.

Not claimed: anything on one routine at two arguments. The head's claims `claimJoin` and
`claimPolicy` read the request through their argument: what is shown is that each, at ONE value of
it, gives the same from two states. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksRespHand

set_option autoImplicit false

namespace OnBytes.Flat

/-! ### `OnBytes.Model.Forest.objects`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Forest.objects (g : OnBytes.Model.Forest.Heard) :
    Resp.K (OnBytes.Model.Forest.objects g) := by
  resp

/-! ### `OnBytes.Model.Head.claimSquares`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Head.U3at (R : OnBytes.Model.Head.Run) (t i : Nat) :
    Resp.K (OnBytes.Model.Head.U3at R t i) := by
  resp

theorem RespOf.OnBytes.Model.Head.tabAt (R : OnBytes.Model.Head.Run) (n : String) :
    Resp.K (OnBytes.Model.Head.tabAt R n) := by
  resp

theorem RespOf.OnBytes.Model.layerObject (o : OnBytes.Model.Level) :
    Resp.K (OnBytes.Model.layerObject o) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimSquares (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimSquares R) := by
  resp

/-! ### `OnBytes.Model.Head.claimLedger`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Head.row5At (R : OnBytes.Model.Head.Run) (P : String) :
    Resp.K (OnBytes.Model.Head.row5At R P) := by
  resp

theorem RespOf.OnBytes.Model.Head.rowAt (R : OnBytes.Model.Head.Run) (P : String) :
    Resp.K (OnBytes.Model.Head.rowAt R P) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimLedger4 (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimLedger4 R) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimLedger5 (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimLedger5 R) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimLedger (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimLedger R) := by
  resp

/-! ### `OnBytes.Model.Head.claimStream`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Head.segOf (R : OnBytes.Model.Head.Run) (sn : String) :
    Resp.K (OnBytes.Model.Head.segOf R sn) := by
  resp

theorem RespOf.OnBytes.Model.Head.xbA (R : OnBytes.Model.Head.Run) (t kh : Nat) :
    Resp.K (OnBytes.Model.Head.xbA R t kh) := by
  resp

theorem RespOf.OnBytes.Model.Head.ewh (R : OnBytes.Model.Head.Run) (sn : String) :
    Resp.K (OnBytes.Model.Head.ewh R sn) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimStream (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimStream R) := by
  resp

/-! ### `OnBytes.Model.Head.claimJoin`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Forest.joinAdded (g : OnBytes.Model.Forest.Heard) :
    Resp.K (OnBytes.Model.Forest.joinAdded g) := by
  resp

theorem RespOf.OnBytes.Model.Forest.paddingLaid (g : OnBytes.Model.Forest.Heard)
    (laid : Array Nat) : Resp.K (OnBytes.Model.Forest.paddingLaid g laid) := by
  resp

theorem RespOf.OnBytes.Model.Head.Sl (R : OnBytes.Model.Head.Run) (sn : String)
    (OFF nl J : Nat) : Resp.K (OnBytes.Model.Head.Sl R sn OFF nl J) := by
  resp

theorem RespOf.OnBytes.Model.Head.ewOf (R : OnBytes.Model.Head.Run) (sn : String) :
    Resp.K (OnBytes.Model.Head.ewOf R sn) := by
  resp

theorem RespOf.OnBytes.Model.Head.gapAt (R : OnBytes.Model.Head.Run) (P : String)
    (i : Nat) (wsum : OnBytes.E) : Resp.K (OnBytes.Model.Head.gapAt R P i wsum) := by
  resp

theorem RespOf.OnBytes.Model.Head.lowDigit (R : OnBytes.Model.Head.Run) (sn : String)
    (wR : OnBytes.E) : Resp.K (OnBytes.Model.Head.lowDigit R sn wR) := by
  resp

theorem RespOf.OnBytes.Model.Head.middleDigit (R : OnBytes.Model.Head.Run)
    (sn : String) (wR : OnBytes.E) :
    Resp.K (OnBytes.Model.Head.middleDigit R sn wR) := by
  resp

theorem RespOf.OnBytes.Model.Head.sh2 (R : OnBytes.Model.Head.Run) (t j : Nat) :
    Resp.K (OnBytes.Model.Head.sh2 R t j) := by
  resp

theorem RespOf.OnBytes.Model.Head.ztSeg (R : OnBytes.Model.Head.Run) (sn : String) :
    Resp.K (OnBytes.Model.Head.ztSeg R sn) := by
  resp

theorem RespOf.OnBytes.Model.Forest.join (g : OnBytes.Model.Forest.Heard)
    (KF : Array OnBytes.Model.Aff) : Resp.K (OnBytes.Model.Forest.join g KF) := by
  resp

theorem RespOf.OnBytes.Model.Head.LINE (R : OnBytes.Model.Head.Run) (sn : String) :
    Resp.K (OnBytes.Model.Head.LINE R sn) := by
  resp

theorem RespOf.OnBytes.Model.Head.keyForm (R : OnBytes.Model.Head.Run) (q : Nat)
    (laid : Array Nat) : Resp.K (OnBytes.Model.Head.keyForm R q laid) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimJoin (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimJoin R) := by
  resp

/-! ### `OnBytes.Model.Head.claimPolicy`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Head.claimPolicy (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimPolicy R) := by
  resp

/-! ### `OnBytes.Model.Head.claimPlanes`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Forest.planesAdded (g : OnBytes.Model.Forest.Heard) :
    Resp.K (OnBytes.Model.Forest.planesAdded g) := by
  resp

theorem RespOf.OnBytes.Model.Forest.planesAt (g : OnBytes.Model.Forest.Heard)
    (lm e : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Resp.K (bit a a_1)) :
    Resp.K (OnBytes.Model.Forest.planesAt g lm e bit) := by
  resp

theorem RespOf.OnBytes.Model.SubM.must (b : Bool) :
    Resp.K (OnBytes.Model.SubM.must b) := by
  resp

theorem RespOf.OnBytes.Model.Forest.planeClaims (g : OnBytes.Model.Forest.Heard)
    (lm : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (pin : Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Resp.K (bit a a_1)) :
    (∀ (a : Nat), Resp.K (pin a)) →
      Resp.K (OnBytes.Model.Forest.planeClaims g lm bit pin) := by
  resp

theorem RespOf.OnBytes.Model.Forest.planeLins (g : OnBytes.Model.Forest.Heard)
    (lm : Nat) (bit : Nat → Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (pin : Nat → OnBytes.Model.SubM OnBytes.Model.Aff)
    (h : ∀ (a a_1 : Nat), Resp.K (bit a a_1)) :
    (∀ (a : Nat), Resp.K (pin a)) →
      Resp.K (OnBytes.Model.Forest.planeLins g lm bit pin) := by
  resp

theorem RespOf.OnBytes.Model.Head.claimPlanes (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimPlanes R) := by
  resp

/-! ### `OnBytes.Model.Head.claimLogits`, and what its text reaches -/

theorem RespOf.OnBytes.Model.Head.claimLogits (R : OnBytes.Model.Head.Run) :
    Resp.K (OnBytes.Model.Head.claimLogits R) := by
  resp

/-! ### `OnBytes.Model.wsForkLin`, and what its text reaches -/

theorem RespOf.OnBytes.Model.wsForkLin (o : OnBytes.Model.WsMerged) :
    Resp.K (OnBytes.Model.wsForkLin o) := by
  resp

/-! ### `OnBytes.Model.HTailF2.linJoin9`, and what its text reaches -/

theorem RespOf.OnBytes.Model.SubM.get {α : Type} (x : Option α) :
    Resp.K (OnBytes.Model.SubM.get x) := by
  resp

theorem RespOf.OnBytes.Model.HTailF2.linJoin9 (tl : OnBytes.Model.HTailF2) :
    Resp.K tl.linJoin9 := by
  resp

/-! ### `OnBytes.Model.HTailF2.linBits9`, and what its text reaches -/

theorem RespOf.OnBytes.Model.HTailF2.linBits9 (tl : OnBytes.Model.HTailF2) :
    Resp.K tl.linBits9 := by
  resp

end OnBytes.Flat
