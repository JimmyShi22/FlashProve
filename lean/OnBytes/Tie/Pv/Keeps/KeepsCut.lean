-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsCut.lean: the rounds of the first chain's view, cut into the stretches
that the calls of the first chain's block have begun, in the run of an accepted proof file.

Definitions, statements and proofs. The relation Kept (OnBytes/Tie/Pv/Keeps/KeepsKit.lean) says of
the context before a routine and the one behind it that the view's rounds not yet begun behind it
are the last of those before it. So the rounds that were begun between two contexts are a list
that is read off the two contexts, and these lists add up.
Main names:
  `used c c'`: the rounds that are not yet begun in c and are begun, or over, in c'.
  `left_of_kept`: the rounds not yet begun in c are `used c c'` and then those not yet begun in c'.
  `used_append`: the stretch from a to c is the stretch from a to b and then that from b to c.
  `used_drop`: a stretch by numbers: so many rounds of the first context's list are dropped, and so
    many of the rest are taken.
  `took_of_kept`: between two contexts in which no message is open, `used c c'` is what was taken
    (`Took`, OnBytes/Tie/Pv/Psc/PscView.lean).
  `kept_parts`: the three parts of one call of runLinkH are Kept, each by itself.
  `fileRan_kept`: so are the calls of the first chain's block.
  `fileRan_cut`: the view's rounds are the five stretches of ChainCheck.start, the links,
    ChainCheck.finish, the first part of the test on the table, and the seal.
  `fileRan_link_cut`: the links' stretch, cut at the link at place j: the links before it; its first
    call, its routine, its row on the table; the links behind it.
Limits: a round counts to the stretch in which it was begun. That a stretch's last round was also
closed in it is said only where no message is open at the stretch's end (`took_of_kept`), which is a
premise there. Hypothesis: every link's routine keeps (AllKeep,
OnBytes/Tie/Pv/Keeps/KeepsLinks.lean). The first chain alone.
-/
import OnBytes.Tie.Pv.Reply.ReplyRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Cut

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5 OnBytes.PscRun

/-- The rounds that are not yet begun in c and are begun, or over, in c'. -/
def used (c c' : Ctx) : List Fmt.RoundView := c.ch.left.take (c.ch.left.length - c'.ch.left.length)

theorem left_of_kept {c c' : Ctx} (k : Kept c c') : c.ch.left = used c c' ++ c'.ch.left := by
  have e := List.suffix_iff_eq_drop.1 k.left
  have h := (List.take_append_drop (c.ch.left.length - c'.ch.left.length) c.ch.left).symm
  rw [← e] at h
  exact h

theorem used_length (c c' : Ctx) :
    (used c c').length = c.ch.left.length - c'.ch.left.length := by
  unfold used
  rw [List.length_take]
  omega

/-- Stretches add up. -/
theorem used_append {a b c : Ctx} (h1 : Kept a b) (h2 : Kept b c) :
    used a c = used a b ++ used b c := by
  have e1 := left_of_kept h1
  have e2 := left_of_kept h2
  have e3 := left_of_kept (h1.trans h2)
  rw [e1, e2, ← List.append_assoc] at e3
  exact (List.append_cancel_right e3).symm

/-- A stretch by numbers. -/
theorem used_drop {c0 c : Ctx} (h0 : Kept c0 c) (c' : Ctx) :
    used c c' = (c0.ch.left.drop (c0.ch.left.length - c.ch.left.length)).take
      (c.ch.left.length - c'.ch.left.length) := by
  rw [← List.suffix_iff_eq_drop.1 h0.left]
  rfl

/-- Between two contexts in which no message is open. -/
theorem took_of_kept {c c' : Ctx} (k : Kept c c') (h : Clean c) (h' : Clean c') :
    Took c (used c c') c' := ⟨h, h', left_of_kept k⟩

/-- The three parts of one call of runLinkH. -/
theorem kept_parts {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} {l : Nat}
    {X : LinkH} [k : KeepsM X.run] {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
    {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck} {o : Option WsForkOut}
    {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) :
    Kept c c1 ∧ Kept c1 c2 ∧ Kept c2 c' := by
  refine ⟨Keeps.out (b := check.first) c chk c1 S.first,
    Keeps.out (self := k.out _ _) c1 ((o, C'), F') c2 S.run, ?_⟩
  by_cases hf : X.fv = true
  · obtain ⟨o', row, _, hr, _⟩ := S.row hf
    exact Keeps.out (b := pendingRowH wsLay r.2.indexMasks o' X.NCL p.lin) c2 row c' hr
  · rw [(S.noRow hf).1]
    exact Kept.refl _

section File

variable {Z : Array LinkH} {c : Params.ProofChains} {table : Params.TableName} {copy : Nat}
  {request words : ByteArray} {reply : E} {wsLay : WsLay} {file : ByteArray} {r : Proof.ProofRead}
  {fin : Proof.FirstEnd} {cE : Ctx} {check0 : ChainCheck} {ca : Ctx}
  {rN : ChainCheck × Proof.LinksResult} {cb cc : Ctx} {lin : LinFirst} {cd : Ctx}

/-- The calls of the first chain's block. -/
theorem fileRan_kept (hk : AllKeep Z)
    (R : FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd) :
    Kept (startOf (Proof.firstStart c.first) r.first.view) ca ∧ Kept ca cb ∧ Kept cb cc ∧
      Kept cc cd ∧ Kept cd cE :=
  ⟨Keeps.out (b := ChainCheck.start c.first.shape c.first.layout) _ _ _ R.start,
    Reply.kept_chain (fun Y hY => hk Y (Array.mem_toList_iff.1 hY)) R.links,
    Keeps.out (b := rN.1.finish) _ _ _ R.finish,
    Keeps.out (b := memberFirstVerify c.first.lin rN.2.indexMasks rN.2.pending) _ _ _ R.member,
    (KeepsM.keeps (Proof.firstEnd lin)).out _ _ _ R.sealing⟩

/-- The view's rounds are the five stretches. -/
theorem fileRan_cut (hk : AllKeep Z)
    (R : FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd) :
    r.first.view.rounds =
      used (startOf (Proof.firstStart c.first) r.first.view) ca ++ used ca cb ++ used cb cc ++
        used cc cd ++ used cd cE := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := fileRan_kept hk R
  have hE : cE.ch.left = [] := by
    have h := R.nothingLeft
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2
  have e := left_of_kept ((((k1.trans k2).trans k3).trans k4).trans k5)
  rw [hE, List.append_nil, used_append (((k1.trans k2).trans k3).trans k4) k5,
    used_append ((k1.trans k2).trans k3) k4, used_append (k1.trans k2) k3, used_append k1 k2] at e
  exact e

/-- The links' stretch, cut at the link at place j. -/
theorem fileRan_link_cut (hk : AllKeep Z)
    (R : FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd)
    (j : Nat) (X : LinkH) (hj : Z.toList[j]? = some X) :
    ∃ checkJ outJ c0 r1 cm chk o C' F' c1 c2,
      LinksChain Z c.first wsLay cE (Z.toList.take j) 0 check0 {} ca (checkJ, outJ) c0 ∧
      LinkStep Z c.first wsLay cE (0 + j) X checkJ outJ c0 r1 cm chk o C' F' c1 c2 ∧
      LinksChain Z c.first wsLay cE (Z.toList.drop (j + 1)) (0 + j + 1) r1.1 r1.2 cm rN cb ∧
      used ca cb = used ca c0 ++ (used c0 c1 ++ used c1 c2 ++ used c2 cm) ++ used cm cb := by
  obtain ⟨checkJ, outJ, c0, r1, cm, chk, o, C', F', c1, c2, A, S, _, _, B⟩ :=
    LinksChain.split R.links j X hj
  have kA : Kept ca c0 :=
    Reply.kept_chain (fun Y hY => hk Y (Array.mem_toList_iff.1 (List.mem_of_mem_take hY))) A
  have kB : Kept cm cb :=
    Reply.kept_chain (fun Y hY => hk Y (Array.mem_toList_iff.1 (List.mem_of_mem_drop hY))) B
  haveI := hk X (Array.mem_toList_iff.1 (List.mem_of_getElem? hj))
  obtain ⟨q1, q2, q3⟩ := kept_parts S
  refine ⟨checkJ, outJ, c0, r1, cm, chk, o, C', F', c1, c2, A, S, B, ?_⟩
  rw [used_append (kA.trans ((q1.trans q2).trans q3)) kB, used_append kA ((q1.trans q2).trans q3),
    used_append (q1.trans q2) q3, used_append q1 q2]

end File

end OnBytes.Tie.Pv.Keeps.Cut

#print axioms OnBytes.Tie.Pv.Keeps.Cut.left_of_kept
#print axioms OnBytes.Tie.Pv.Keeps.Cut.used_append
#print axioms OnBytes.Tie.Pv.Keeps.Cut.used_drop
#print axioms OnBytes.Tie.Pv.Keeps.Cut.took_of_kept
#print axioms OnBytes.Tie.Pv.Keeps.Cut.fileRan_cut
#print axioms OnBytes.Tie.Pv.Keeps.Cut.fileRan_link_cut
