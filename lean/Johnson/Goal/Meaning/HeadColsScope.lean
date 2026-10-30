-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadColsScope.lean: at all public files in the goals' scope the head's layout
gives each of its six lookup calls the number of column coordinates that the output head's own text
reckons for that call.

What the file holds. X: what publicOf returns on public files in scope.
  place_lJ        the logarithm of the columns of a placed call: enough for the sum of its segments'
                  lengths, and at least the floor.
  calls_six       where the call lines are the stored example's six, callsOf returns these six
                  calls.
  kind_cols       the kind's number (Johnson/Desc/Kinds/HeadIn.lean: lJ) at sizes with lt = 10,
                  ls = 6, d = 5120, V = 202048 and the floor 27: 18, 18, 18, 17, 17, 17.
  layout_cols     the layout's number in scope: the same six.
  cols_in_scope   **for q < 6: (X.HLy.calls.getD q default).lJ =
                  lJ (Head.keyFloor X.hS) (callKeys q) at sizesOf X.hS.**
Why. The program `verify-on-bytes` and the quiet step that makes the tables of reads cut a call's
key point by the layout's number (OnBytes/Model/HeadHeard.lean: zjOf, ztOf); the head's own text
cuts it by its own (fromLookup; given's third test). Where the two numbers are one, so are the cuts.

On what it rests. Johnson/Goal/Meaning/HeadCallsScope.lean (lines_in_scope), HeadCondScope.lean
(numbers_in_scope), HeadForInScope.lean (keyFloor_in_scope); Johnson/Road/HeadLaid.lean
(admittedH_of_layout: JV, JVa, calls); Johnson/Road/FormsKeysPos.lean (piecesBelow_total).

Letters under "there is": none.
What it does not give. Nothing outside the scope: the numbers are the full size's. Nothing on the
size of a key point in a verifier's state. Nothing on soundness.

-/
import Johnson.Goal.Meaning.HeadCallsScope
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Road.FormsKeysPos
import Johnson.Desc.Kinds.HeadCallLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open OnBytes.Model (place SegAsk CallD topBit piecesBelow)
open OnBytes.Model.Head (Shape HL callsOf callLines callsFrom lineSegs segments keyFloor)

/-- The logarithm of the columns of a placed call. -/
theorem place_lJ (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hb : ∀ n ∈ asks.map (·.2.1), n < 2 ^ (topBit + 1)) :
    (place name kind asks fl).lJ = max (OnBytes.ceilLog2 (asks.map (·.2.1)).sum) fl := by
  show max (OnBytes.ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl = _
  rw [OnBytes.Road.piecesBelow_total _ _ hb]

/-- Where the call lines are the stored example's six, these are the calls. -/
theorem calls_six {h : Shape} {L : HL} {cs : List CallD} (hc : callsOf h L = .ok cs)
    (hl : callLines h = VerifierAndGoals.Lines.callsHRef) :
    cs = [place "R16a" "R16" [("NF", h.d, false), ("NFH", h.d, false), ("HD0", L.JV, false)]
            (keyFloor h - h.lt),
          place "R16b" "R16" [("HD1", L.JV, false)] (keyFloor h - h.lt),
          place "R8" "R8" [("ROW", OnBytes.Model.ledNRH h.XL, false), ("HD2", L.JV, false)]
            (keyFloor h - h.lt),
          place "FEa" "FE" [("HE0", L.JVa, false)] (keyFloor h - h.lt),
          place "FEb" "FE" [("HE1", L.JV - L.JVa, false)] (keyFloor h - h.lt),
          place "FC" "FC" [("CNF", h.d, false)] (keyFloor h - h.lt)] := by
  unfold callsOf at hc
  rw [hl] at hc
  obtain ⟨-, hc⟩ := OnBytes.Road.Hd.ok_of_needed hc
  dsimp only at hc
  have e : callsFrom (segments h L) (keyFloor h - h.lt) VerifierAndGoals.Lines.callsHRef [] [] =
      some ([place "R16a" "R16" [("NF", h.d, false), ("NFH", h.d, false), ("HD0", L.JV, false)]
            (keyFloor h - h.lt),
          place "R16b" "R16" [("HD1", L.JV, false)] (keyFloor h - h.lt),
          place "R8" "R8" [("ROW", OnBytes.Model.ledNRH h.XL, false), ("HD2", L.JV, false)]
            (keyFloor h - h.lt),
          place "FEa" "FE" [("HE0", L.JVa, false)] (keyFloor h - h.lt),
          place "FEb" "FE" [("HE1", L.JV - L.JVa, false)] (keyFloor h - h.lt),
          place "FC" "FC" [("CNF", h.d, false)] (keyFloor h - h.lt)],
        ["CNF", "HE1", "HE0", "HD2", "ROW", "HD1", "HD0", "NFH", "NF"]) := by
    rfl
  rw [e] at hc
  obtain ⟨-, hc⟩ := OnBytes.Road.Hd.ok_of_needed hc
  exact (Except.ok.inj hc).symm

/-- The six numbers. -/
def colsRef : List ℕ := [18, 18, 18, 17, 17, 17]

/-- Sizes with the four numbers that the kind's number of columns reads; 0 elsewhere. -/
@[reducible] def sRef : Sizes :=
  { lt := 10, ls := 6, d := 5120, MF := 0, KF := 0, epsF := 0, V := 202048, sh := 0, F := 0 }

/-- Lean's kernel evaluates it. -/
theorem ref_cols : ∀ q, q < 6 → @lJ sRef 27 (callKeys q) = colsRef.getD q 0 := by
  decide +kernel

/-- The kind's number at the full size's sizes. -/
theorem kind_cols (S : Sizes) (h1 : S.lt = 10) (h2 : S.ls = 6) (h3 : S.d = 5120)
    (h4 : S.V = 202048) : ∀ q, q < 6 → @lJ S 27 (callKeys q) = colsRef.getD q 0 := by
  cases S with
  | @mk toS V sh F =>
    cases toS with
    | mk lt ls d MF KF epsF =>
      dsimp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      intro q hq
      have e : @lenOf (@Sizes.mk (FinalNorm.Sizes.mk 10 6 5120 MF KF epsF) 202048 sh F) =
          @lenOf sRef := by
        funext k
        cases k with
        | inl a => cases a <;> rfl
        | inr a => cases a <;> rfl
      rw [← ref_cols q hq]
      show max (clog2 ((callKeys q).map
        (@lenOf (@Sizes.mk (FinalNorm.Sizes.mk 10 6 5120 MF KF epsF) 202048 sh F))).sum)
        (27 - 10) = _
      rw [e]
      rfl

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The layout's number in scope. -/
theorem layout_cols (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    ∀ q, q < 6 → (X.HLy.calls.getD q default).lJ = colsRef.getD q 0 := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have A := OnBytes.Road.Hd.admittedH_of_layout B.head
  obtain ⟨cs, hc, -, hL⟩ := A.calls
  have N := numbers_in_scope hZ hR h
  have kf := Meaning.HeadS.keyFloor_in_scope hZ hR h
  have six := calls_six hc (lines_in_scope hZ hR h)
  have eS : X.hS.S2 = 64 := by
    show 2 ^ (X.hS.la - X.hS.lt) = 64
    rw [N.la, N.lt]
  have eJV : X.HLy.JV = 202048 := by
    rw [A.JV, N.V, eS]
    rfl
  have eJVa : X.HLy.JVa = 131072 := by
    rw [A.JVa, eJV]
    rfl
  rw [N.d, N.XL, N.lt, kf, eJV, eJVa] at six
  intro q hq
  rw [hL, six]
  interval_cases q
  all_goals
    show (place _ _ _ _).lJ = _
    rw [place_lJ _ _ _ _ (by decide)]
    rfl

/-- **The layout's number of column coordinates is the kind's, at each of the six calls.** -/
theorem cols_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : ∀ q, q < 6 →
    (X.HLy.calls.getD q default).lJ = @lJ (sizesOf X.hS) (keyFloor X.hS) (callKeys q) := by
  intro q hq
  have N := numbers_in_scope hZ hR h
  rw [layout_cols hZ hR h q hq, Meaning.HeadS.keyFloor_in_scope hZ hR h]
  refine (kind_cols (sizesOf X.hS) N.lt ?_ N.d N.V q hq).symm
  show X.hS.la - X.hS.lt = 6
  rw [N.la, N.lt]

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.place_lJ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_six
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.ref_cols
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.kind_cols
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.layout_cols
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.cols_in_scope
