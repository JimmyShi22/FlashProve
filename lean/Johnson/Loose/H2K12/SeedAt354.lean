-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/SeedAt354.lean:
THE LAW OF THE PROXIMITY
TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN: THE SECOND FACT ALONG "REACHED" AT THE
BORDER IN FRONT OF THE TEST: the sendings' invariant K1.SeedIs (Johnson/Desc/K1/Law/SeedIs.lean) at
each member of the group under test; and with it ALL SIX FACTS that the first half of the fourth tie
takes from "reached" (FactsK12, H2K12/Promise354.lean). Statements and proofs: a joining.

The law itself is K2.seedIs_behind (Johnson/Top/H0/Tw/K2C/SeedIsBehind.lean):
behind an accept of the code switch's decision, at every NEW message with one
answer.
What is joined here:
  seed_behind_place   at the place of the last code switch (finishPlace,
                  Johnson/Top/H0/Tw/K2C/Finish.lean). EVERY MEMBER OF THE GROUP IS A NEW MESSAGE OF
                  THIS SWITCH: the place's own quiet step in front pushes the group, fresh, and
                  names it (finishFrontQ_st, finishFrontQ_fr, Johnson/Top/H0/Tw/K2C/FinFront.lean);
                  the switch joins its own new messages to it and nothing else (yes_finish_groups,
                  Johnson/Top/H0/Tw/K2C/GroupsAtYes.lean). THE FACTOR READS AS A UNIT: the switch
                  refuses the zero element as words, and every word shown is below the prime
                  (isZeroE_iff, OnBytes/Slice/ProgField.lean; okE_ofTriple,
                  Johnson/Desc/K1/Law/OkView.lean). The quiet step behind leaves the statement.
  seed_of_reach   along "reached" (H2K12/GroupAt354.lean), AT THE LISTED
                  MEMBER's SHAPE: the message's shape is the listed one (msgShape_at,
                  Johnson/Desc/K12/Door/MsgShapes.lean).
  factsK12_of_reach   FactsK12 from FoldFacts (Johnson/Desc/First/FoldFacts.lean) at any condition
                  Rch that gives "reached by the sub-protocols' own steps, each behind the test that
                  every word is below the prime".
Limits. (1) A JOINING OVER LETTERS. SeatF1, FoldFacts and p.grp = N.groupAt n are premises. (2) TWO
PREMISES ON THE LISTS: hM: the list of shapes has, at a listed member's number, that member's shape
· hTie: K1.Tie (one answer; the codes' lengths; the shape's and the pad's tests) AT EVERY MEMBER OF
THE LIST ms: more than is spent: FactsK12 has no promise in hand that says at which seat a member of
the group sits. Where one member of ms fails it the statements are idle. (3) WHETHER ALL PREMISES
CAN BE MET TOGETHER IS SHOWN NOWHERE HERE. No soundness statement. Nothing on hiding.

-/
import Johnson.Top.H0.Tw.K2C.SeedIsBehind
import Johnson.Top.H0.Tw.K2C.GroupsAtYes
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Desc.K1.Law.OkView
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Loose.H2K12.GroupAt354
import Johnson.Loose.H2K12.Promise354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-- **Behind an accept at the place of the last code switch, where every word shown is below the
prime: each member of the group that the switch's numbers name is a message with a shape at which,
if the three tests on the codes and the shape pass and it counts one answer (K1.Tie), the sendings'
invariant K1.SeedIs holds.** -/
theorem seed_behind_place (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {cols : List (ℕ × ℕ × List UInt64)}
    (hv : VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, cols⟩ = true)
    (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') :
    ∀ G0, s'.st.groups[p.grp]? = some G0 → ∀ o ∈ G0.members.toList,
      ∃ sh, (s'.st.oracles[o]?).map (·.shape) = some sh ∧
        (VerifiableInference.Desc.K1.Tie s'.st.codes sh →
          ∃ ρ y, VerifiableInference.Desc.K1.SeedIs s'.st.codes sh s'.st o ρ y) := by
  obtain ⟨t, t', rs', gs', h1, h2, h3, hsub⟩ := finishPlace_cut p h
  obtain ⟨r₁, r₂, a, G, w, roots, rfl, F⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h2
  obtain ⟨a', m, -, -, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  obtain ⟨x, y, S3, Y, rows, Gx, c, A⟩ :=
    VerifiableInference.Desc.First.K2.yes_whole p t r₁ r₂ gs' t' h2
  -- the front
  have hx : x = VerifiableInference.Desc.First.K2.finFrontOf t a G := by
    have e := A.front
    unfold VerifiableInference.Desc.First.K2.frontAt at e
    rw [hp, F.hHere] at e
    have e' : a.G.map (fun G => VerifiableInference.Desc.First.K2.finFrontOf t a G) = some x := e
    rw [F.hLaid] at e'
    exact (Option.some.inj e').symm
  -- the group is fresh in front of the switch
  obtain ⟨a₁, G₁, ha₁, -, -, -, -, -, -, -, -, hg₁⟩ :=
    VerifiableInference.Desc.First.K2.finishFrontQ_fr h1
  obtain rfl : a₁ = a := by
    rw [F.hHere] at ha₁
    injection ha₁ with e
    exact e.symm
  have hfresh : t.st.groups[a₁.fr.group]? = some (VerifiableInference.Desc.First.K2.freshGroup
      s.check.frame.shape.code s.check.frame.shape.maskCode) := by
    rw [VerifiableInference.Desc.First.K2.finishFrontQ_st h1, hg₁]
    simp [VerifiableInference.Desc.First.K2.withFresh]
  obtain ⟨a₂, G₂, ha₂, hG₂, hgain⟩ := VerifiableInference.Desc.First.K2.yes_finish_groups hp h2
  obtain rfl : a₂ = a₁ := by
    rw [F.hHere] at ha₂
    injection ha₂ with e
    exact e.symm
  obtain rfl : G₂ = G := Option.some.inj (hG₂.symm.trans F.hLaid)
  obtain ⟨-, -, Ga, Gb, hGa, hGb, hmem, -⟩ := hgain _ hfresh rfl rfl
  obtain rfl := Option.some.inj (hfresh.symm.trans hGa)
  -- the code switch's own law
  obtain ⟨bits, answers, seeds, -, hall⟩ := VerifiableInference.Desc.First.K2.seedIs_behind h2 A
  have hc : t'.st.codes = x.st.codes := A.tables.codes.trans (A.same.codes.trans A.sent.codes)
  intro G0 hG0 o ho
  have hG0' : t'.st.groups[a₂.fr.group]? = some G0 := by rw [F.hGrp]; exact hG0
  obtain rfl : Gb = G0 := Option.some.inj (hGb.symm.trans hG0')
  -- the member is a new message
  have hnew : ∃ i n, o = x.st.oracles.size + i ∧
      (_root_.Tw.K2.switchNotices x.T x.others)[i]? = some n := by
    rw [hmem] at ho
    have ho' : o ∈ (VerifiableInference.Desc.First.K2.switchGain
        (VerifiableInference.Desc.First.K2.finFrontOf t a₂ G₂)).map (·.1) := by
      simpa [VerifiableInference.Desc.First.K2.freshGroup] using ho
    rw [← hx] at ho'
    unfold VerifiableInference.Desc.First.K2.switchGain at ho'
    rw [List.map_cons, List.mem_cons] at ho'
    rcases ho' with rfl | ho'
    · exact ⟨0, ⟨x.T.shape, x.T.leafClass⟩, rfl, by simp [_root_.Tw.K2.switchNotices]⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ho'
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      have h5 := (List.of_mem_zip hq').1
      obtain ⟨j, hj, e⟩ := List.mem_map.1 h5
      have hj' : j < x.T.kept.size := List.mem_range.1 hj
      refine ⟨j + 1, ⟨(x.T.kept[j]).shape, (x.T.kept[j]).leafClass⟩, ?_, ?_⟩
      · show q'.1 = _
        rw [← e]
        omega
      · unfold _root_.Tw.K2.switchNotices
        rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by simp)]
        simp [hj']
  obtain ⟨i, n, rfl, hn⟩ := hnew
  have hsh : (t'.st.oracles[x.st.oracles.size + i]?).map (·.shape) = some n.shape := by
    rw [A.tables.shape, A.same.shape, A.sent.shape, hn]
    rfl
  refine ⟨n.shape, hsh, fun hT => ?_⟩
  have hT' : VerifiableInference.Desc.K1.Tie x.st.codes n.shape := hc ▸ hT
  obtain ⟨b, tt, hb, hz, -, hS⟩ := hall i n hn hT'.one hT'.lengths hT'.shape hT'.fits
  have hok : OnBytes.okE b = true := by
    simp only [VerifiableInference.Desc.viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true] at hv
    have h6 := (hv.1 r₁ (hsub r₁ List.mem_cons_self)).1
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hb)
    exact VerifiableInference.Desc.K1.okE_ofTriple u (by simpa using h6 u hu)
  have hne : OnBytes.Slice.readE b ≠ 0 := fun h0 => by
    have := (OnBytes.Slice.isZeroE_iff b hok).2 h0
    rw [hz] at this
    cases this
  show ∃ ρ y, VerifiableInference.Desc.K1.SeedIs t'.st.codes n.shape t'.st _ ρ y
  rw [hc]
  exact ⟨_, _, hS (Units.mk0 _ hne) (Units.val_mk0 hne)⟩

/-- **THE SENDINGS' INVARIANT AT THE MEMBERS OF THE GROUP UNDER TEST, ALONG "REACHED".** -/
theorem seed_of_reach {Cl P : Type} (bs : List (Block S Cl)) (start : P → S) (k : ℕ)
    (B : Block S Cl) (hB : bs[k]? = some B) (p : P2) (hK : SeatF1 B p)
    (N : VerifiableInference.Desc.First.Numbers) (n : ℕ) (hgrp : p.grp = N.groupAt n)
    (cs : OnBytes.Codes) (ms : List VerifiableInference.Desc.Sound.Mem)
    (d : VerifiableInference.Desc.First.FoldData) {z : P} {s' : S}
    (h : Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start (k + 1) (z, s'))
    (hc : s'.st.codes = cs)
    (hSh : VerifiableInference.Desc.K12.Door.atFirstShapes d.M s' = true)
    (hM : ∀ o x, ListedAt ms d.L.places o x → d.M[o]? = some (x.1.l.get x.2).1)
    (hTie : ∀ x ∈ ms, VerifiableInference.Desc.K1.Tie cs (x.1.l.get x.2).1) :
    ∀ G0, s'.st.groups[N.groupAt n]? = some G0 → ∀ o ∈ G0.members.toList,
      ∀ x, ListedAt ms d.L.places o x →
        ∃ ρ yv, VerifiableInference.Desc.K1.SeedIs cs (x.1.l.get x.2).1 s'.st o ρ yv := by
  obtain ⟨s, b, -, hb, hy⟩ := reach_last h
  rw [List.getElem?_map, hB] at hb
  obtain rfl : VerifiableInference.Desc.Sound.below B = b := Option.some.inj hb
  obtain ⟨rs, gs, hv, hd⟩ := seat_yes hK hy
  intro G0 hG0 o ho x hx
  rw [← hgrp] at hG0
  obtain ⟨sh, hsh, hS⟩ := seed_behind_place p hK.1 hv hd G0 hG0 o ho
  have hlt : o < s'.st.oracles.size := by
    obtain ⟨X, hX, -⟩ := Option.map_eq_some_iff.1 hsh
    exact (Array.getElem?_eq_some_iff.1 hX).1
  have e := VerifiableInference.Desc.K12.Door.msgShape_at
    (show VerifiableInference.Desc.K12.Door.msgShapesB d.M s'.st = true from hSh) o hlt
  rw [hsh, hM o x hx] at e
  obtain rfl : sh = (x.1.l.get x.2).1 := Option.some.inj e
  rw [hc] at hS
  exact hS (hTie x hx.1)

/-- **ALL SIX FACTS THAT THE FIRST HALF OF THE FOURTH TIE TAKES FROM "REACHED"** (FactsK12,
H2K12/Promise354.lean), at a state behind the last code switch: from FoldFacts
(Johnson/Desc/First/FoldFacts.lean) at any condition Rch that gives "reached by the sub-protocols'
own steps, each behind the test that every word is below the prime". -/
theorem factsK12_of_reach {Cl P Str : Type} (bs : List (Block S Cl)) (start : P → S) (k : ℕ)
    (B : Block S Cl) (hB : bs[k]? = some B) (p : P2) (hK : SeatF1 B p)
    (N : VerifiableInference.Desc.First.Numbers) (n : ℕ) (hgrp : p.grp = N.groupAt n)
    (cs : OnBytes.Codes) (ms : List VerifiableInference.Desc.Sound.Mem)
    (d : VerifiableInference.Desc.First.FoldData) (hcs : d.sent.codes = cs)
    {reqW : P → Array UInt32} {links : List VerifiableInference.Desc.First.ModelPart}
    {ps : List VerifiableInference.Desc.Place}
    (Rch : ℕ → (P × S) × Str → Prop)
    (hR : ∀ j a, Rch j a → Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start j a.1)
    (hf : VerifiableInference.Desc.First.FoldFacts Rch (fun a => a.1) d reqW links ps)
    (hM : ∀ o x, ListedAt ms d.L.places o x → d.M[o]? = some (x.1.l.get x.2).1)
    (hTie : ∀ x ∈ ms, VerifiableInference.Desc.K1.Tie cs (x.1.l.get x.2).1)
    (a : (P × S) × Str) (hr : Rch (k + 1) a) (hm : a.1.2.failed = none) :
    FactsK12 d N n cs ms a.1.2 :=
  factsK12_of_fold hf N n cs ms (k + 1) a hr hm
    (fun o ho =>
      (group_of_reach bs start k B hB p hK (z := a.1.1) (s' := a.1.2) (hR _ a hr) o ho).trans hgrp)
    (seed_of_reach bs start k B hB p hK N n hgrp cs ms d (z := a.1.1) (s' := a.1.2) (hR _ a hr)
      ((hf.codes (k + 1) a hr hm).trans hcs) (hf.msgShapes (k + 1) a hr hm) hM hTie)

end H2K12

#print axioms H2K12.seed_behind_place
#print axioms H2K12.seed_of_reach
#print axioms H2K12.factsK12_of_reach
