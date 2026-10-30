-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/ScdTop.lean: the port's routine for the sumcheck by degrees, where it succeeds,
has heard a transcript of the typed block, and its record is the block's output on that transcript,
read.

keyAtIndexIn (OnBytes/Model/AttentionDivide.lean) draws the element that batches the pairs, receives
the messages of the sumcheck by degrees and makes its row. Neither that routine nor the typed block
of Cb/Pv/Att/Scd.lean tests a value, so the tie between the two is an equality of outputs.

Main names:
  `ended_pscAt`: the record behind the round of the end values has the weights, the challenges and
    the running claim that `PscAt` (OnBytes/Tie/Pv/Psc/PscTie.lean) asks for.
  `scdRow_ok`: scdRow leaves the context as it was; its row is the record's row form at the given
    summand; it puts the coefficients of the hiding polynomial under their slots.
  `scd_summand`: the summand at which keyAtIndexIn makes its row, read, is the typed summand at the
    reading of the challenges and of the end values.
  `scd_block_out`: the typed block's verifier, on the transcript that is made from what the port has
    heard, puts out `plainOut` (OnBytes/Tie/Pv/Att/Tr.lean).
  `scd_tie`: if keyAtIndexIn succeeds from a state whose arrays on slots have their length, and the
    sumcheck before it has at least lt + lgk challenges, then for every reading, all parameters T at
    the shape's sizes and every state st: the rounds heard are those of the block's listener
    (`Parts`); the record's start, target, first slot and sEnd are named; the row is the record's
    row form at a summand s0; the record is as `PscAt` asks; and if the reading of beta is not 0:
    the port's rounds are read as the transcript made from them (`ReadsAs`); `plainOut` on what was
    heard has eps, the last value, the point and the end values of the port's record, read; and if
    T's public points and factors at st are the readings of the port's, the typed summand at the
    output's point and values is the reading of s0.

Limits: one direction: from the routine's success. That the reading of beta is not 0 is a premise.
What the row form is worth is not said here: it follows from these facts by `row_iff_UHolds`
(OnBytes/Tie/Pv/Psc/PscTie.lean), under a choice of the places of the mask entries and of the
incoming form, which stay parameters here (OnBytes/Tie/Pv/Att/RowTie.lean). What the slots of the
end values are worth is not said here and does not follow from `scd_tie`, which says nothing of the
state that the routine leaves: OnBytes/Tie/Pv/Att/TiesFull.lean states the tie with that state.
-/
import OnBytes.Tie.Pv.Att.Seams
import OnBytes.Tie.Pv.Att.Tr
import OnBytes.Tie.Pv.Att.ScdTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Psc (Weight hearMany)

theorem extract_getD (r : Array E) (i j a : Nat) (h : i + a < j) :
    (r.extract i j).getD a zeroE = r.getD (i + a) zeroE := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rename_i hn
    have : r.size ≤ i + a := by omega
    rw [Array.getElem?_eq_none this]

theorem toList_getD (r : Array E) (l : List E) (h : r.toList = l) (i : Nat) :
    r.getD i zeroE = l.getD i zeroE := by
  subst h
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem snd_getD (rs : List (List E × E)) (i : Nat) :
    (rs.map (·.2)).getD i zeroE = (rs.getD i ([], zeroE)).2 := by
  simp [List.getD_eq_getElem?_getD]
  cases rs[i]? <;> rfl

theorem scdNum_lt (s : ScdSize) (a : s.A) : scdNum s a < s.Lam + s.pairs * s.lt := by
  cases a with
  | inl l =>
    have := l.2
    show l.1 < _
    omega
  | inr x =>
    obtain ⟨b, t⟩ := x
    have hb : (b.1 + 1) * s.lt ≤ s.pairs * s.lt := Nat.mul_le_mul_right _ b.2
    have ht := t.2
    show s.Lam + b.1 * s.lt + t.1 < _
    rw [Nat.add_mul, Nat.one_mul] at hb
    omega

theorem ended_pscAt {p : Psc} {C : Aff} {τ mu eps : E} {first : Nat} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E}
    (a : Ended p C τ mu eps first ws rs dY sentY beta) :
    PscAt p (ws ++ [Weight.atZero (dY + 1)]) (rs ++ [(sentY, beta)]) mu where
  vars := a.vars
  r := by rw [a.r, List.map_append]; rfl
  claim := by rw [a.claim, a.eps, a.target]

theorem scdRow_ok (o1 o : Attention.Scd) (s0 : E) (F G : Fork) (c c' : Ctx)
    (h : scdRow o1 s0 F c = .ok ((o, G), c')) (hs : Sized F) :
    c' = c ∧ o.rowU = o1.p.rowForm s0 {} ∧ o.p = { o1.p with rowMade := true } ∧ o.r = o1.r ∧
      o.sEnd = o1.sEnd ∧
      Filled F G o1.p.first (List.replicate o1.p.walk.1.length zeroE) (subE zeroE oneE) := by
  unfold scdRow at h
  obtain ⟨⟨row, p'⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k1
  obtain ⟨a1, a2, a3, a4⟩ := pscRow_filled o1.p p' s0 {} row F F1 c c1 h1 hs
  rw [e1, e2, e3]
  exact ⟨a1, a2, a3, rfl, rfl, a4⟩

section Summand
variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem scd_summand (S : Attention.Shape) (T : Cb.Pv.Att.Scd K (ofShape S)) (st : T.St)
    (fr om4 r : Array E)
    (rs : List (List E × E)) (sh : Nat → E) (hsz : S.cf.lt + S.cf.lgk ≤ fr.size)
    (hri : ∀ a : Fin S.cf.lt, T.ri st a = ρ.val (fr.getD a.1 zeroE))
    (hrg : ∀ a : Fin S.cf.lgk, T.rg st a = ρ.val (fr.getD (S.cf.lt + a.1) zeroE))
    (hom : ∀ b : Fin (ofShape S).pairs, T.om st b = ρ.val (om4.getD b.1 zeroE))
    (hr : r.toList = rs.map (·.2)) (z : Fin (ofShape S).k → K)
    (hz : ∀ i, z i = ρ.val (rs.getD i.1 ([], zeroE)).2) :
    ρ.val (keyFlat S.cf.lt S.Lam S.HA S.NP (fr.extract 0 S.cf.lt)
        (fr.extract S.cf.lt (S.cf.lt + S.cf.lgk)) (r.extract 0 S.cf.lt)
        (r.extract S.cf.lt (S.cf.lt + S.cf.lgk))
        (r.extract (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk)) om4 sh) =
      T.plain.S st z fun a => ρ.val (sh (scdNum (ofShape S) a)) := by
  have hget : ∀ i, ρ.val (r.getD i zeroE) = ρ.val (rs.getD i ([], zeroE)).2 := fun i => by
    rw [toList_getD r _ hr, snd_getD]
  refine (keyFlat_read ρ (ofShape S) _ _ _ _ _ om4 sh
    (by rw [Array.size_extract]; show min S.cf.lt fr.size - 0 = S.cf.lt; omega)
    (by rw [Array.size_extract]; show min (S.cf.lt + S.cf.lgk) fr.size - S.cf.lt = S.cf.lgk; omega)
    z
    (fun a => by
      have : a.1 < S.cf.lt := a.2
      rw [hz, extract_getD r 0 S.cf.lt a.1 (by omega), hget, Nat.zero_add]
      rfl)
    (fun a => by
      have : a.1 < S.cf.lgk := a.2
      rw [hz, extract_getD r S.cf.lt (S.cf.lt + S.cf.lgk) a.1 (by omega), hget]
      rfl)
    (fun a => by
      have : a.1 < S.cf.lt := a.2
      rw [hz, extract_getD r (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk) a.1 (by omega), hget]
      rfl)).trans ?_
  have e1 : (fun a : Fin (ofShape S).lt => ρ.val ((fr.extract 0 S.cf.lt).getD a.1 zeroE)) =
      T.ri st := funext fun a => by
    have : a.1 < S.cf.lt := a.2
    rw [hri, extract_getD fr 0 S.cf.lt a.1 (by omega), Nat.zero_add]
  have e2 : (fun a : Fin (ofShape S).lgk =>
      ρ.val ((fr.extract S.cf.lt (S.cf.lt + S.cf.lgk)).getD a.1 zeroE)) = T.rg st :=
    funext fun a => by
      have : a.1 < S.cf.lgk := a.2
      rw [hrg, extract_getD fr S.cf.lt (S.cf.lt + S.cf.lgk) a.1 (by omega)]
  have e3 : (fun b : Fin (ofShape S).pairs => ρ.val (om4.getD b.1 zeroE)) = T.om st :=
    funext fun b => (hom b).symm
  rw [e1, e2, e3]
  rfl

/-- The typed block's verifier on the transcript that is made from what the port has heard, with n
further scalars r in the first message: it puts out the statement, r and `plainOut`. -/
theorem scd_block_out {s : ScdSize} (T : Cb.Pv.Att.Scd K s) (st : T.St) (target mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : s.A → K)
    (n : ℕ) {X : Type} (cl : X → (Fin n → K) → K × T.St) (Ex : ExtSpec) (x : X) (y : Ex.Str)
    (r : Fin n → K) (hcl : cl x r = (ρ.val target, st)) :
    (scdR T n cl Ex).out x y
        (((), (r, ρ.val mu)), ρ.val eps, plainTr ρ T.plain rs sentY beta hβ vals) =
      some ((x, r), plainOut ρ T.plain st target mu eps rs sentY beta hβ vals) := by
  rw [scd_out]
  show some ((x, r), shortV T.plain.our.par T.plain.fix (cl x r) _) = _
  rw [hcl]
  rfl

/-- the end values, read, under their names -/
def scdVals (s : ScdSize) (v : List E) : s.A → K := fun a => ρ.val (v.getD (scdNum s a) zeroE)

theorem scd_tie (S : Attention.Shape) (scF : Sc3) (o : Attention.Scd) (F G : Fork) (c c' : Ctx)
    (h : keyAtIndexIn S scF F c = .ok ((o, G), c')) (hz : Sized F)
    (hsz : S.cf.lt + S.cf.lgk ≤ scF.r.size) (T : Cb.Pv.Att.Scd K (ofShape S)) (st : T.St) :
    ∃ (om4 : Array E) (c1 : Ctx) (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E)
      (v : List E) (s0 : E),
      coinsOm S.NP F c = .ok ((om4, F), c1) ∧
      F.publicPart (weightedSum S.NP om4 (sc3B scF)) = some τ ∧
      Parts c1 c1 c' [] mu o.p.eps (S.scdDegrees.map fun d => Weight.plain (d + 1)) rs
        (S.cf.lt + 1) sentY beta v ∧
      v.length = S.Lam + S.NP * S.cf.lt ∧ o.r.toList = rs.map (·.2) ∧
      o.p.start = weightedSum S.NP om4 (sc3B scF) ∧ o.p.target = τ ∧ o.p.first = F.next ∧
      o.sEnd = F.next + (1 + S.scdDegrees.sum) + (S.cf.lt + 1) ∧
      o.rowU = o.p.rowForm s0 {} ∧
      PscAt o.p (plainWs (List.ofFn T.plain.deg) T.plain.DY) (rs ++ [(sentY, beta)]) mu ∧
      ∀ hβ : ρ.val beta ≠ 0,
        ReadsAs ρ (rs ++ [(sentY, beta)]) T.plain.our.par.fmt [pRoundV K T.plain.our.par.A]
          (plainTr ρ T.plain rs sentY beta hβ (scdVals ρ (ofShape S) v)) ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).eps =
          ρ.val o.p.eps ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).fin =
          ρ.val o.p.claim ∧
        (∀ i : Fin (ofShape S).k, ldPartIni (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt i =
            ρ.val (o.r.getD i.1 zeroE)) ∧
        ldPartLast (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt =
            ρ.val beta ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).vals =
          scdVals ρ (ofShape S) v ∧
        ((∀ a : Fin S.cf.lt, T.ri st a = ρ.val (scF.r.getD a.1 zeroE)) →
          (∀ a : Fin S.cf.lgk, T.rg st a = ρ.val (scF.r.getD (S.cf.lt + a.1) zeroE)) →
          (∀ b : Fin (ofShape S).pairs, T.om st b = ρ.val (om4.getD b.1 zeroE)) →
          T.plain.S st
            (ldPartIni (ofShape S).k (ofShape S).deg (pDummy K (S.cf.lt + 1))
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).pt)
            (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (scdVals ρ (ofShape S) v)).vals =
          ρ.val s0) := by
  obtain ⟨om4, F1, c1, o1, F2, c2, h1, h2, h3⟩ := keyAtIndexIn_flat S scF o F G c c' h
  have hF1 : F1 = F := ((liftY_ok (trBatch S.NP) F F1 c c1 om4).1 h1).2
  rw [hF1] at h1 h2
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, _, _, a11, a12⟩ :=
    scdIn_seam _ _ _ _ o1 F F2 c1 c2 h2 hz
  obtain ⟨b1, b2, b3, b4, b5, _⟩ := scdRow_ok o1 o _ F2 G c2 c' h3 a12.sized
  have hε : o.p.eps = o1.p.eps := by rw [b3]
  have hcl : o.p.claim = o1.p.claim := by rw [b3]
  have hdeg : List.ofFn T.plain.deg = S.scdDegrees := scd_degrees_shape S
  have hl : rs.map (·.1.length) = List.ofFn T.plain.deg := by rw [hdeg]; exact a5
  have hat := ended_pscAt a3
  have hws : plainWs (List.ofFn T.plain.deg) T.plain.DY =
      (S.scdDegrees.map fun d => Weight.plain (d + 1)) ++ [Weight.atZero (S.cf.lt + 1 + 1)] := by
    unfold plainWs
    rw [hdeg]
    rfl
  have hsh : ∀ a : (ofShape S).A,
      shownAt F2 o1.sEnd (scdNum (ofShape S) a) = v.getD (scdNum (ofShape S) a) zeroE := fun a => by
    have hlt : scdNum (ofShape S) a < v.length := by rw [a7]; exact scdNum_lt (ofShape S) a
    unfold shownAt
    rw [a12.shown _ hlt]
    rfl
  refine ⟨om4, c1, τ, mu, rs, sentY, beta, v,
    keyFlat S.cf.lt S.Lam S.HA S.NP (scF.r.extract 0 S.cf.lt)
      (scF.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)) (o1.r.extract 0 S.cf.lt)
      (o1.r.extract S.cf.lt (S.cf.lt + S.cf.lgk))
      (o1.r.extract (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk)) om4 (shownAt F2 o1.sEnd),
    h1, a1, ?_, a7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hε, b1]
    exact a2
  · rw [b4]
    exact a4
  · rw [b3]
    exact a3.start
  · rw [b3]
    exact a3.target
  · rw [b3]
    exact a3.first
  · rw [b5]
    exact a11
  · rw [b2, b3]
    rfl
  · rw [hws, b3]
    exact ⟨hat.vars, hat.r, hat.claim⟩
  · intro hβ
    refine ⟨plain_reads ρ T.plain rs sentY beta hβ _ hl a6, rfl, ?_, ?_,
      plain_last ρ T.plain st _ _ _ rs sentY beta hβ _,
      plain_vals ρ T.plain st _ _ _ rs sentY beta hβ _, ?_⟩
    · rw [plain_fin ρ T.plain st _ _ _ rs sentY beta hβ _ (scd_ok T).one hl a6, hws, hcl, a3.claim,
        hε]
    · intro i
      rw [b4, toList_getD o1.r _ a4, snd_getD]
      exact plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i
    · intro hri hrg hom
      rw [plain_vals, scd_summand ρ S T st scF.r om4 o1.r rs _ hsz hri hrg hom a4 _
        (fun i => plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i)]
      congr 1
      funext a
      show ρ.val _ = ρ.val _
      rw [hsh a]

end Summand

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.scdRow_ok
#print axioms OnBytes.Tie.Pv.Att.scd_summand
#print axioms OnBytes.Tie.Pv.Att.scd_block_out
#print axioms OnBytes.Tie.Pv.Att.scd_tie
