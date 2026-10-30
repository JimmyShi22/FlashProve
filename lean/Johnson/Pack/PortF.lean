-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/PortF.lean: a message over the base field whole; the signature of a sending as a
function of the programs' own records; what it asks, on numbers alone.

Definitions, statements and proofs. Johnson/Pack/PortZ.lean shows the sample map a zero-evader where
the pad is one place in a row over the extension field. The other case of a shape is: no mask row,
main rows over the base field. Then the pad is three places over the base field under 1, x, x², and
the whole message is over the base field. The library has that case (`OMsg.JohnF`,
Cb/Req1/LdReqJohnSub.lean). With both cases, the sampled messages of one sending are a signature
whose members have short lists, evading samples and the laws.
Main names:
  `CaseF`, `tauZ_inj`, `padValF_inj`, `portZ_okOnF`: under `CaseF` the sample map is a zero-evader
    on the vectors over the base field (`Cb.Gl.gl_padBasis`).
  `port_genIn`: the code of every shape has its generator over the base field.
  `port_fmtF`, `port_johnFZ`: under `CaseF` every word as sent is over the base field as read; the
    oracle message is `OMsg.JohnF`.
  `PadFits`, `MeetsAt cs s e d L`: what is asked of a shape at the radius e: `PBase`, and either 2 e
    < d, or one answer, `CaseE` or `CaseF`, a row long enough for the pad, `InJohnson`, and L the
    library's `listMax`.
  `sigOf cs l`: the signature of a sending; l lists the sampled messages' shapes with their radii.
  `sigOf_holes`, `sigOf_send`, `sigOf_floor`: under `MeetsAt` at every member: lists, evasion, laws;
    knowledge soundness of the sending for every fair way to draw the seeds; the preamble's item at
    `sigLeft C (sigOf cs l) Cl holds`.
Limits: the limits of Johnson/Pack/PortZ.lean hold here too. The list is meant for the messages that
are sampled. A message without an answer meets only the arm 2 e < d, which fails at a radius beyond
unique decoding: such messages (masks that are sent ahead of the round that uses them) are no
members of this signature, and nothing is said of them here. One answer a message. Codes of at most
2^32 positions. The radii are arguments, and so is the way to draw the seeds
(Johnson/Pack/PortS.lean defines one). No list of the programs' shapes stands in this file. Nothing
on the honest prover or on hiding.
-/
import Johnson.Pack.PortZ
import Cb.Req1.LdReqJohnSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

section
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape)

/-- No mask row, and main rows over the base field: the whole message is over the base field. -/
def CaseF : Prop := s.maskRows = 0 ∧ s.mainDeg = 1

/-- The number of a pad's place. -/
def tauZ (j : {j // padP cs s j}) : Fin 3 := ⟨padNo cs s j.1 % 3, Nat.mod_lt _ (by decide)⟩

theorem wZ_eq (j : {j // padP cs s j}) : wZ cs s j = Cb.Gl.padW (tauZ cs s j) := rfl

theorem each_three (h : CaseF s) : eachZ s = 3 := by
  unfold eachZ
  rw [if_neg (by rw [h.2]; decide)]

theorem tauZ_inj (h : CaseF s) : Function.Injective (tauZ cs s) := by
  intro a b e
  have e' : padNo cs s a.1 % 3 = padNo cs s b.1 % 3 := congrArg Fin.val e
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have h3 := each_three s h
  refine Subtype.ext ?_
  rcases a with x | x <;> rcases b with y | y
  · have e2 : (x.2.val + eachZ s - (pMain cs s).ell) % 3 =
        (y.2.val + eachZ s - (pMain cs s).ell) % 3 := e'
    have h1 := ha.2.1
    have h2 := hb.2.1
    have h4 := ha.2.2
    have h5 := hb.2.2
    have h6 : x.2.val < (pMain cs s).ell := x.2.isLt
    have h7 : y.2.val < (pMain cs s).ell := y.2.isLt
    exact congrArg Sum.inl (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · exfalso
    have hy : y.1.val < s.maskRows := y.1.isLt
    have hz := h.1
    omega
  · exfalso
    have hx : x.1.val < s.maskRows := x.1.isLt
    have hz := h.1
    omega
  · exfalso
    have hx : x.1.val < s.maskRows := x.1.isLt
    have hz := h.1
    omega

theorem padValF_inj (h : CaseF s) : Function.Injective (padVal (F := GF) (wZ cs s)) := by
  have hτ := tauZ_inj cs s h
  have key : ∀ c : {j // padP cs s j} → GF, padVal (F := GF) (wZ cs s) c =
      padVal (F := GF) Cb.Gl.padW fun u => ∑ j, if tauZ cs s j = u then c j else 0 := by
    intro c
    unfold padVal
    simp only [map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (tauZ cs s j)]
    · rw [if_pos rfl, wZ_eq]
    · intro u _ hu
      rw [if_neg (fun e => hu e.symm), map_zero, mul_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  intro c c' e
  rw [key, key] at e
  have e2 := Cb.Gl.gl_padBasis.1 e
  funext j
  have pick : ∀ d : {j // padP cs s j} → GF,
      (∑ i, if tauZ cs s i = tauZ cs s j then d i else 0) = d j := by
    intro d
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg fun e => hi (hτ e)]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [← pick c, ← pick c']
  exact congrFun e2 (tauZ cs s j)

/-- Under `CaseF` the sample map is a zero-evader on the vectors over the base field. -/
theorem portZ_okOnF (h : CaseF s) :
    (portZ cs s).OKOn fun v => ∀ j, v j ∈ Set.range (algebraMap GF GE) := by
  have hon := Cb.ood_okOn_comap GE _ _ _ (sigmaZ cs s) (PadInF GF)
    (Cb.ood_okOn_pad GF GE (Fin (bitsZ cs s)) {j // ¬ padP cs s j} {j // padP cs s j} GEˣ _
      (wZ cs s) Units.val (plc_inj cs s) (fun _ _ e => Units.ext e) (padValF_inj cs s h))
  exact fun v hv hne => hon v (fun _ => hv _) hne

/-! ### The generator and the format -/

theorem ldOf_enc_mem (C : Fmt.M1.Code) (a : ℕ) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (hm : ∀ j, m j ∈ (algebraMap GF GE).range) (hr : ∀ q, r q ∈ (algebraMap GF GE).range)
    (p : Fin (2 ^ C.a)) : (ldOf C a).enc m r p () ∈ (algebraMap GF GE).range := by
  show (∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j ∈ _
  exact Subring.add_mem _
    (Subring.sum_mem _ fun q _ => Subring.mul_mem _ ⟨_, rfl⟩ (hr q))
    (Subring.sum_mem _ fun j _ => Subring.mul_mem _ ⟨_, rfl⟩ (hm j))

theorem unit_mem {ι : Type} [DecidableEq ι] (j i : ι) :
    (Pi.single j (1 : GE) : ι → GE) i ∈ (algebraMap GF GE).range := by
  rw [Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/-- The code of every shape has its generator over the base field. -/
theorem port_genIn : (portCode cs s).GenIn GF := by
  intro x α i
  rcases α with α | α <;> rcases i with j | q
  · exact ldOf_enc_mem (cMain cs s) (aOf cs s) _ _ (fun _ => unit_mem _ _)
      (fun _ => Subring.zero_mem _) _
  · exact ldOf_enc_mem (cMain cs s) (aOf cs s) _ _ (fun _ => Subring.zero_mem _)
      (fun _ => unit_mem _ _) _
  · exact ldOf_enc_mem (cMask cs s) (aOf cs s) _ _ (fun _ => unit_mem _ _)
      (fun _ => Subring.zero_mem _) _
  · exact ldOf_enc_mem (cMask cs s) (aOf cs s) _ _ (fun _ => Subring.zero_mem _)
      (fun _ => unit_mem _ _) _

theorem port_fmtF (h : CaseF s) (e : ℕ) (f : (portOmZ cs s e).Str) :
    (portOmZ cs s e).C.LongIn GF ((portOmZ cs s e).upW f) := by
  intro x α
  rcases α with α | α
  · show upRow (s.mainDeg == 1) (f (.inl (posIn (cMain cs s) x)) (α.1, ())) ∈ _
    generalize f (.inl (posIn (cMain cs s) x)) (α.1, ()) = y
    revert y
    have hb : (s.mainDeg == 1) = true := by rw [h.2]; rfl
    show ∀ y : RowTy (s.mainDeg == 1), upRow (s.mainDeg == 1) y ∈ _
    rw [hb]
    exact fun y => ⟨y, rfl⟩
  · exfalso
    have hx : α.1.val < s.maskRows := α.1.isLt
    have hz := h.1
    omega

theorem port_johnFZ (e d L : ℕ) (g : PBase cs s d)
    (hJ : InJohnson (Fintype.card (Fin (2 ^ aOf cs s))) d e)
    (hL : L = listMax (Fintype.card (Fin (2 ^ aOf cs s))) d e) (h : CaseF s) :
    (portOmZ cs s e).JohnF GF d L :=
  ⟨port_laws cs s g.ok, port_dist cs s g.ok d g.d1 g.d2, hJ, hL, port_genIn cs s,
    port_fmtF cs s h e, portZ_okOnF cs s h⟩

/-! ### What is asked of a shape -/

/-- The row that bears the pad is long enough for it. Where it is not, `OnBytes.Send.pad` gives
nothing and the block SEND fails. -/
def PadFits : Prop :=
  if 0 < s.maskRows then 1 ≤ (pMask cs s).ell else eachZ s ≤ (pMain cs s).ell

/-- What is asked of a shape at a radius: conditions on numbers alone. -/
def MeetsAt (e d L : ℕ) : Prop :=
  PBase cs s d ∧
    ((2 * e < d ∧ L = 1) ∨
      (s.answers = 1 ∧ (CaseE s ∨ CaseF s) ∧ PadFits cs s ∧
        InJohnson (Fintype.card (Fin (2 ^ aOf cs s))) d e ∧
        L = listMax (Fintype.card (Fin (2 ^ aOf cs s))) d e))

theorem omZ_mem (e d L : ℕ) (g : MeetsAt cs s e d L) : Cb.Pack.MemOK GF (portOmZ cs s e) d L := by
  rcases g.2 with h | h
  · rw [h.2]
    exact Or.inl (Or.inl (port_half cs s e _ _ d g.1 h.1))
  · rcases h.2.1 with c | c
    · exact Or.inl (Or.inr (port_johnZ cs s e d L g.1 h.2.2.2.1 h.2.2.2.2 c))
    · exact Or.inr (port_johnFZ cs s e d L g.1 h.2.2.2.1 h.2.2.2.2 c)

end

/-- The signature of a sending: a function of the codes and of the list of the sampled messages'
shapes, each with its radius. -/
noncomputable def sigOf (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) : Sig GE where
  O := Fin l.length
  om := fun i => portOmZ cs (l.get i).1 (l.get i).2

theorem sigOf_holes (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (d Ls : Fin l.length → ℕ) (g : ∀ i, MeetsAt cs (l.get i).1 (l.get i).2 (d i) (Ls i)) :
    Cb.Pack.HList (sigOf cs l) Ls ∧ Cb.Pack.HEvades (sigOf cs l) ∧ Cb.Pack.HLaws (sigOf cs l) :=
  Cb.Pack.holes_of_members GF (sigOf cs l) d Ls fun i => omZ_mem cs _ _ _ _ (g i)

theorem sigOf_send (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (d Ls : Fin l.length → ℕ) (g : ∀ i, MeetsAt cs (l.get i).1 (l.get i).2 (d i) (Ls i))
    (Sd : (sigOf cs l).Seeds) (hF : Sd.Fair) (Kc X W W' : Type) (E₀ : ExtSpec)
    (A : Rels Kc X E₀ W) (back : (sigOf cs l).Msg → W' → W) :
    (ldSendFam (sigOf cs l) Sd X E₀).red.KnowInto A.on
      ((sigOf cs l).over ((sigOf cs l).pull A back)).on A.relR
      ((sigOf cs l).over ((sigOf cs l).pull A back)).relR
      (fun _ _ w => back ((sigOf cs l).msgs w.1) w.2) (Cb.Pack.sendErr (sigOf cs l) Sd Ls X E₀) :=
  Cb.Pack.send_knowInto (sigOf cs l) Sd Kc X W W' E₀ A back Ls hF
    (sigOf_holes cs l d Ls g).1 (sigOf_holes cs l d Ls g).2.1

/-- What the preamble leaves: `sigLeft` at `sigOf`. One sending, closed: the item on knowledge
soundness of a preamble (`Cb.Pack.floor_preKnow` at N := sigOf cs l). -/
theorem sigOf_floor (C : Hiop.ConfigurationWithOutOfDomainSample) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (d Ls : Fin l.length → ℕ) (g : ∀ i, MeetsAt cs (l.get i).1 (l.get i).2 (d i) (Ls i))
    (Sd : (sigOf cs l).Seeds) (hF : Sd.Fair) (Kc Wi Wr Cl Wp : Type)
    (holds : Cl → C.Rec → C.Msg → (sigOf cs l).Msg → Prop) (A : Rels Kc (Cl × C.Rec) C.E0 Wi)
    (back : (sigOf cs l).Msg → Wp → Wi) (RiR : (Cl × C.Rec) × C.E0.Str → Wr → Prop)
    (fr : Wi → Wr) (z0 : Wp) (r0 : (sigOf cs l).Rnd)
    (h1 : ∀ a m U, C.dcd a.2 a.1.2 = some U → holds a.1.1 a.1.2 U m → A.relR a (back m z0))
    (h2 : ∀ a, A.on a → ¬ C.coll a.2 a.1.2.1)
    (h3 : ∀ a w, A.on a → A.relR a w → RiR a (fr w)) :
    Hiop.PreKnowR (sigLeft C (sigOf cs l) Cl holds)
      (closeF (ldSendFam (sigOf cs l) Sd (Cl × C.Rec) C.E0)) A.on RiR
      (fun _ _ m => fr (back ((sigOf cs l).msgs ((sigOf cs l).pair m r0)) z0))
      (Cb.Pack.sendErr (sigOf cs l) Sd Ls (Cl × C.Rec) C.E0) :=
  Cb.Pack.floor_preKnow C (sigOf cs l) Sd Kc Wi Wr Cl Wp holds A back Ls RiR fr z0 r0 hF
    (sigOf_holes cs l d Ls g).1 (sigOf_holes cs l d Ls g).2.1 h1 h2 h3

end Johnson.Pack

#print axioms Johnson.Pack.sigOf_floor
#print axioms Johnson.Pack.padValF_inj
#print axioms Johnson.Pack.portZ_okOnF
#print axioms Johnson.Pack.port_genIn
#print axioms Johnson.Pack.port_johnFZ
#print axioms Johnson.Pack.sigOf
#print axioms Johnson.Pack.sigOf_holes
#print axioms Johnson.Pack.sigOf_send
