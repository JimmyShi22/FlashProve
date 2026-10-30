-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/P2AtTable.lean: code switching (K2): THE FIELD hp OF THE KIND's CONDITION
(Johnson/Top/H0/K2Ties/Assembly.lean: «the place's numbers are the typed structure's»:
K2Caller.P2At r p) AT THE MADE TABLE's OWN ROWS: entry m of the table of typed structures that is
made of the three public files (K2Caller.tableOf) and the numbers that the kind's lot makes for
the switch into group m + 1 declare the same two entries. A join; every step a call. NO BLOCK
IMPORTS THIS FILE.
  prep_is        what prepOf lays, by its text: the sizes are the plan's own; the list of
                 the groups' numbers is Plan.framesOf of these sizes and of the sub-proofs off the
                 ground's public data; the sizes' shape is the ground's first chain's
  later_is       entry m of that list without its first entry is entry m + 1 of the whole list:
                 out of later_l and framesFrom_l
                 (Johnson/Top/H0/K2Ties/RowsAddr.lean)
  p2At_table     tableOf pol lay KL = .ok t · pubPlain secondHashFunction pol lay KL = .ok Zp · blankBy mk Zp
                 = some G₀ · prepOf Zp G₀ = some P · t[m]? = some r · the place's link stands for
                 group m + 1 · numsAt P a.link = some n ⟹ P2At r (IM.k2P Zp a nm st n)
WHY A BRIDGE IS WANTED. tableOf reads the three files anew by the planner of verify-on-bytes
(Verify.planned); Zp is the plain one's value: LinkJoin.made_tie
(Johnson/Desc/First/Link/Law/RowsOfMade.lean) has that the two share the public data and the
sizes.
WHAT STAYS FOR hp AT THE CONSTANT's TERMS. t = tableFullLit (the accept of tableWrittenB:
evaluated, no theorem) · ProofFile.pAtK2 Zp m = IM.k2P Zp … n (seated_is_pAt, PAtSeated.lean, under
spotsFitB). Not here. No example. No soundness is claimed.
-/
import Johnson.P1K2R.SitsLaw
import Johnson.Top.H0.K2Ties.RowsAddr
import Johnson.Top.H0.Opts.TableFrom
import Johnson.Desc.First.Link.Law.RowsOfMade
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Params OnBytes.Plan
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.K2Caller (SwRow P2At tableOf tableFrom tableOf_iff rowOf)
open VerifiableInference.Desc.First.K2Ties (later_l framesFrom_l)

theorem prep_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : Prep} (h : prepOf Z G = some P) :
    P.z = Z.p.chains.made.sized.proof ∧
      P.frames = framesOf P.z (Model.Verify.subproofsWith G.W G.first.shape.link) ∧
      P.z.request = G.first.shape := by
  unfold prepOf prepareAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  · rename_i ht
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨trees, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    have ht' : tied Z.p.chains.made.sized.proof G.first Z.s₀.st.codes Z.s₀.check.frame.shape
        Z.P.samples = true := by simpa using ht
    unfold tied at ht'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
    exact ⟨rfl, rfl, ht'.1.1.1.1⟩

theorem later_is (z : ProofSized) (sub : Subproofs) {m : Nat} {f : FrameN}
    (h : ((framesOf z sub).filter fun n => n.l != 0)[m]? = some f) :
    (framesOf z sub)[m + 1]? = some f := by
  have hmem : f ∈ framesOf z sub := (List.mem_filter.1 (List.mem_of_getElem? h)).1
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hmem
  have e1 := later_l z sub m f h
  have e2 : f.l = 0 + j := framesFrom_l z _ 0 _ _ _ j f (by unfold framesOf at hj; exact hj)
  obtain rfl : j = m + 1 := by omega
  exact hj

theorem p2At_table {pol lay KL : ByteArray} {t : List SwRow} (hT : tableOf pol lay KL = .ok t)
    {Zp : ProofFile.Pub} (hpub : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) {mk : ProofFile.LinksBy}
    {G₀ : ProofFile.Ground} (hG : ProofFile.blankBy mk Zp = some G₀) {P : Prep}
    (hP : prepOf Zp G₀ = some P) {m : Nat} {r : SwRow} (hr : t[m]? = some r) {a : Place}
    {nm : String} {st : VerifiableInference.Desc.First.K2.At} {n : Nums}
    (ha : a.link.getD P.z.request.link.length = m + 1) (hn : numsAt P a.link = some n) :
    P2At r (IM.k2P Zp a nm st n) := by
  obtain ⟨p, R, hp, _, rfl⟩ := tableOf_iff.1 hT
  obtain ⟨eX, eS, _⟩ := VerifiableInference.Desc.LinkJoin.made_tie hpub hp
  obtain ⟨ez, ef, er⟩ := prep_is hP
  have hW := ProofFile.Law.blankBy_W hG
  have hz : p.chains.made.sized.proof = P.z := by
    rw [ez, eS]
    rfl
  unfold tableFrom at hr
  rw [List.getElem?_map] at hr
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hr
  have hf1 := later_is _ _ hf
  obtain ⟨f', _, hf', _, _, _, hall⟩ := k2P_p2At (Z := Zp) (a := a) (nm := nm) (st := st) hn
  rw [ha, ef, hW, ← er] at hf'
  rw [hz, eX] at hf1
  obtain rfl : f = f' := Option.some.inj (hf1.symm.trans hf')
  rw [hz]
  exact hall _ _ _

end P1K2

#print axioms P1K2.prep_is
#print axioms P1K2.later_is
#print axioms P1K2.p2At_table
