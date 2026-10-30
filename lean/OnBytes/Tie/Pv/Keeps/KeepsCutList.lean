-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsCutList.lean: the stretch of the first chain's view that the links have
begun, as one list of stretches, one for each link; and that a call of runLinkH, and a chain of such
calls, is determined by where it began.

Statements and proofs, over OnBytes/Tie/Pv/Keeps/KeepsCut.lean.
Main names:
  `LinkStep.unique`: two records of one call of runLinkH from one state of the calls, one result and
    one context name the same values and contexts.
  `LinksChain.unique`: the same for the calls over a list of links.
  `used_self`: no round lies between a context and itself.
  `linksChain_list`: there is a list with one stretch for each link whose stretches, laid behind
    each other, are the stretch of the whole chain; and whoever has the chain before the link at
    place j and that link's step, with whatever names, finds at place j of the list that step's
    three stretches: of the first call, of the link's routine, of the row on the table.
  `fileRan_list`: the same for the run of an accepted file.
Limits: those of OnBytes/Tie/Pv/Keeps/KeepsCut.lean.
-/
import OnBytes.Tie.Pv.Keeps.KeepsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Cut

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5 OnBytes.PscRun

theorem linksResult_ext {a b : Proof.LinksResult} (h1 : a.indexMasks = b.indexMasks)
    (h2 : a.pending = b.pending) (h3 : a.reply = b.reply) : a = b := by
  cases a
  cases b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- One call of runLinkH is determined by where it began. -/
theorem LinkStep.unique {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd cEnd' : Ctx}
    {l : Nat} {X : LinkH} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
    {r r' : ChainCheck × Proof.LinksResult} {c' c'' : Ctx} {chk chk' : ChainCheck}
    {o o' : Option WsForkOut} {C' C'' : LinkCtx} {F' F'' : Fork} {c1 c1' c2 c2' : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (S' : LinkStep links p wsLay cEnd' l X check out c r' c'' chk' o' C'' F'' c1' c2') :
    r = r' ∧ c' = c'' ∧ c1 = c1' ∧ c2 = c2' := by
  have e1 := S.first.symm.trans S'.first
  obtain ⟨rfl, rfl⟩ : chk = chk' ∧ c1 = c1' := Prod.mk.inj (Except.ok.inj e1)
  have e2 := S.run.symm.trans S'.run
  obtain ⟨rfl, rfl, rfl, rfl⟩ : o = o' ∧ C' = C'' ∧ F' = F'' ∧ c2 = c2' := by
    cases e2
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hm : r.2.indexMasks = r'.2.indexMasks := by
    by_cases h0 : (l == 0) = true
    · exact (Prod.mk.inj (Except.ok.inj ((S.masks h0).symm.trans (S'.masks h0)))).1
    · rw [S.masks' h0, S'.masks' h0]
  have hre : r.2.reply = r'.2.reply := by
    by_cases h2 : (X.kind == 2) = true
    · rw [(S.plainHead h2).2, (S'.plainHead h2).2]
    · rw [(S.plainElse h2).2, (S'.plainElse h2).2]
  have h1 : r.1 = r'.1 := S.next.trans S'.next.symm
  by_cases hf : X.fv = true
  · obtain ⟨a, row, ha, hr, hp⟩ := S.row hf
    obtain ⟨a', row', ha', hr', hp'⟩ := S'.row hf
    obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
    rw [hm] at hr
    obtain ⟨rfl, rfl⟩ : row = row' ∧ c' = c'' := Prod.mk.inj (Except.ok.inj (hr.symm.trans hr'))
    exact ⟨Prod.ext h1 (linksResult_ext hm (hp.trans hp'.symm) hre), rfl, rfl, rfl⟩
  · obtain ⟨q1, q2⟩ := S.noRow hf
    obtain ⟨q1', q2'⟩ := S'.noRow hf
    exact ⟨Prod.ext h1 (linksResult_ext hm (q2.trans q2'.symm) hre), q1.trans q1'.symm, rfl, rfl⟩

/-- The calls over a list of links are determined by where they began. -/
theorem LinksChain.unique {links : Array LinkH} {p : Params.First} {wsLay : WsLay}
    {cEnd cEnd' : Ctx} : ∀ {rest : List LinkH} {l : Nat} {check : ChainCheck}
      {out : Proof.LinksResult} {c : Ctx} {r r' : ChainCheck × Proof.LinksResult} {c' c'' : Ctx},
      LinksChain links p wsLay cEnd rest l check out c r c' →
      LinksChain links p wsLay cEnd' rest l check out c r' c'' → r = r' ∧ c' = c''
  | [], _, _, _, _, _, _, _, _, A, B => by
    obtain ⟨a1, a2⟩ : _ ∧ _ := A
    obtain ⟨b1, b2⟩ : _ ∧ _ := B
    exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  | _ :: _, _, _, _, _, _, _, _, _, A, B => by
    obtain ⟨_, _, _, _, _, _, _, _, S, _, _, T⟩ := A
    obtain ⟨_, _, _, _, _, _, _, _, S', _, _, T'⟩ := B
    obtain ⟨rfl, rfl, _, _⟩ := LinkStep.unique S S'
    exact LinksChain.unique T T'

theorem used_self (c : Ctx) : used c c = [] := by
  unfold used
  rw [Nat.sub_self]
  rfl

/-- One stretch for each link. -/
theorem linksChain_list {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} :
    ∀ (rest : List LinkH), (∀ X ∈ rest, KeepsM X.run) → ∀ (l : Nat) (check : ChainCheck)
      (out : Proof.LinksResult) (c : Ctx) (r : ChainCheck × Proof.LinksResult) (c' : Ctx),
      LinksChain links p wsLay cEnd rest l check out c r c' →
      ∃ Ls : List (List Fmt.RoundView), Ls.length = rest.length ∧ used c c' = Ls.flatten ∧
        ∀ (j : Nat) (X : LinkH) (check0 : ChainCheck) (out0 : Proof.LinksResult) (c0 : Ctx)
          (r1 : ChainCheck × Proof.LinksResult) (cm : Ctx) (chk : ChainCheck)
          (o : Option WsForkOut) (C' : LinkCtx) (F' : Fork) (c1 c2 : Ctx),
          LinksChain links p wsLay cEnd (rest.take j) l check out c (check0, out0) c0 →
          LinkStep links p wsLay cEnd (l + j) X check0 out0 c0 r1 cm chk o C' F' c1 c2 →
          rest[j]? = some X → Ls[j]? = some (used c0 c1 ++ used c1 c2 ++ used c2 cm)
  | [], _, _, _, _, c, _, c', A => by
    obtain ⟨_, e⟩ : _ ∧ _ := A
    refine ⟨[], rfl, by rw [e, used_self]; rfl, ?_⟩
    intro j X _ _ _ _ _ _ _ _ _ _ _ _ _ hj
    cases hj
  | Y :: rest, hk, l, check, out, c, r, c', A => by
    obtain ⟨r1, cm, chk, o, C', F', c1, c2, S, _, _, T⟩ := A
    haveI := hk Y List.mem_cons_self
    have hk' : ∀ X ∈ rest, KeepsM X.run := fun X hX => hk X (List.mem_cons_of_mem _ hX)
    obtain ⟨Ls, h1, h2, h3⟩ := linksChain_list rest hk' (l + 1) r1.1 r1.2 cm r c' T
    obtain ⟨q1, q2, q3⟩ := kept_parts S
    refine ⟨(used c c1 ++ used c1 c2 ++ used c2 cm) :: Ls, by rw [List.length_cons, h1]; rfl, ?_,
      ?_⟩
    · rw [List.flatten_cons, ← h2, used_append ((q1.trans q2).trans q3) (Reply.kept_chain hk' T),
        used_append (q1.trans q2) q3, used_append q1 q2]
    · intro j X check0 out0 c0 r1' cm' chk' o' C'' F'' c1' c2' A' S' hj
      cases j with
      | zero =>
        obtain ⟨a1, a2⟩ : (check0, out0) = (check, out) ∧ c0 = c := A'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj a1
        subst a2
        obtain rfl : Y = X := Option.some.inj hj
        obtain ⟨_, rfl, rfl, rfl⟩ := LinkStep.unique S S'
        rfl
      | succ j =>
        obtain ⟨_, _, _, _, _, _, _, _, S0, _, _, T0⟩ := A'
        obtain ⟨rfl, rfl, _, _⟩ := LinkStep.unique S S0
        have e : l + (j + 1) = l + 1 + j := by omega
        rw [e] at S'
        exact h3 j X check0 out0 c0 r1' cm' chk' o' C'' F'' c1' c2' T0 S' hj

/-- The same for the run of an accepted file. -/
theorem fileRan_list {Z : Array LinkH} (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray} {r : Proof.ProofRead} {fin : Proof.FirstEnd} {cE : Ctx}
    {check0 : ChainCheck} {ca : Ctx} {rN : ChainCheck × Proof.LinksResult} {cb cc : Ctx}
    {lin : LinFirst} {cd : Ctx}
    (R : FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd) :
    ∃ Ls : List (List Fmt.RoundView), Ls.length = Z.size ∧
      r.first.view.rounds =
        used (startOf (Proof.firstStart c.first) r.first.view) ca ++ Ls.flatten ++ used cb cc ++
          used cc cd ++ used cd cE ∧
      ∀ (j : Nat) (X : LinkH) (checkJ : ChainCheck) (outJ : Proof.LinksResult) (c0 : Ctx)
        (r1 : ChainCheck × Proof.LinksResult) (cm : Ctx) (chk : ChainCheck)
        (o : Option WsForkOut) (C' : LinkCtx) (F' : Fork) (c1 c2 : Ctx),
        LinksChain Z c.first wsLay cE (Z.toList.take j) 0 check0 {} ca (checkJ, outJ) c0 →
        LinkStep Z c.first wsLay cE (0 + j) X checkJ outJ c0 r1 cm chk o C' F' c1 c2 →
        Z.toList[j]? = some X → Ls[j]? = some (used c0 c1 ++ used c1 c2 ++ used c2 cm) := by
  obtain ⟨Ls, h1, h2, h3⟩ := linksChain_list Z.toList
    (fun Y hY => hk Y (Array.mem_toList_iff.1 hY)) 0 check0 {} ca rN cb R.links
  exact ⟨Ls, by rw [h1, Array.length_toList], by rw [← h2]; exact fileRan_cut hk R, h3⟩

end OnBytes.Tie.Pv.Keeps.Cut

#print axioms OnBytes.Tie.Pv.Keeps.Cut.LinkStep.unique
#print axioms OnBytes.Tie.Pv.Keeps.Cut.LinksChain.unique
#print axioms OnBytes.Tie.Pv.Keeps.Cut.linksChain_list
#print axioms OnBytes.Tie.Pv.Keeps.Cut.fileRan_list
