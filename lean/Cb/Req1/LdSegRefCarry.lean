-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefCarry.lean: under the hypotheses of its statements, the wide fact on fresh masks is
carried through "read", the range check, the shift and the steps of the reference segment.

Two definitions, statements and proofs. Rules of the framework only; nothing of a text is rendered
here.

Why: zero knowledge of a request asks, at every masked link, that the fact which the link needs is
among the facts that are fresh at its place (Cb/Req1/LdReq.lean: `m.After base`).
Cb/Req1/LdSegCarry.lean shows, move by move, under the hypotheses of its statements, that the wide
fact (`a.wideFact Rd Rr own Mk val`: the entries in Rd, the encoding randomness at Rr, the whole
further witness; the masks at "own") is carried by batchings, splits, locations, sendings and
folds. Here: the two kinds of moves that are missing there, and the lists of moves of
Cb/Req1/LdSegRefRng.lean, Cb/Req1/LdSegRefDig.lean, Cb/Req1/LdSegRefRows.lean.

Main names (Mk is finite and not empty in the statements):
  `Spec.segWide_keep`: a step without rounds over one signature whose honest map keeps the pairs,
    maps the explicit part without looking at the witness, and makes the new further witness from
    the explicit part, the messages and the old further witness ("up"): carried, if "up" reads the
    messages only at entries in Rd that are not own.
  `Spec.segWide_lift`: a reduction on claims about messages, lifted over the oracle messages of a
    stage (`a.lift`): carried, if at the base transcript, new explicit part and new further witness
    read the messages only at entries in Rd that are not own.
  `LdRrD.NoLook`, as `Q.D.NoLook Rd own`: the one condition of the range check's side: the integer
    cells (c.yz of the core) are read off (messages, further witness) without looking at own
    entries or outside Rd. (With the cells riding along as the core, nothing of the messages is
    read at all, in this sense: `A.Xa.Q.D.NoLook Rd own` for all Rd and own:
    `Spec.ldSegRefAll_noLook`, Cb/Req1/LdSegRefAll.lean, under `A.Ghost κ`.)
  `LdSendD.NoLook`: the condition on a sender, as Cb/Req1/LdSegCarry.lean has it: new messages and
    the further witness handed on are made from entries in Rd that are not own, randomness at Rr,
    the further witness and coins.
  `Spec.ldSegRef_rr_carry`: under `D.NoLook Rd own`, `D.d1.Hyp`, `D.d3.Hyp` and `NoLook` of `D.d1`
    and of `D.d3`: through the five moves of "read, then the range check": from D.s0.wideFact Rd Rr
    own .. to D.s4.wideFact, the sets extended to the new names by any RdN, RrN, RdN', RrN'.
  `Spec.ldSegRef_dg_carry`: through the three moves before the digits' lookup (step, shift, step):
    no condition beside the premise that is written out and whatever the arguments hold as proofs.
  `Spec.ldSegRef_ga_carry`: through the step that gathers the rows: no condition beside the premise
    that is written out and whatever the arguments hold as proofs.

Limits: this file says nothing on the lookup's chain and on the batching of tensor rows
(parameters). It does not say that a sender with NoLook exists.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefRowsProofs
import Cb.Req1.LdSegCarry

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

/-- The sender does not look. -/
def LdSendD.NoLook {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (Rd : a.S.Ent → Prop)
    (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) : Prop :=
  ∀ w w' : a.W, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
    (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
    (∀ k, d.D.put w' k = d.D.put w k) ∧ (d.D.rest w').2 = (d.D.rest w).2

/-- The integer cells are read without looking. -/
def LdRrD.NoLook {E Kc : Type} [Field E] {E₀ : ExtSpec} {Wp : Type}
    (D : LdRrD E Kc E₀ Wp) (Rd own : D.S.Ent → Prop) : Prop :=
  ∀ (m m' : D.S.Msg) (wp : Wp),
    D.S.Alike Rd own m m' → D.c.yz (D.A₀.core (m', wp)) = D.c.yz (D.A₀.core (m, wp))

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

/-- A step over one signature that keeps the pairs. -/
def segWide_keep : Prop :=
  ∀ (S : Sig E) (St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec) (A : Rels Kc St E₀ (S.Msg × Wp))
      (A' : Rels Kc St' E₀' (S.Msg × Wp')) (f : St × S.Smp → Option (St' × S.Smp))
      (g : ExtMap (E₀.prod S.ext) (E₀'.prod S.ext))
      (m : (St × S.Smp) × (S.Wit × Wp) → (St' × S.Smp) × (S.Wit × Wp'))
      (back : (St × S.Smp) × (E₀.prod S.ext).Str → S.Wit × Wp' → S.Wit × Wp)
      (φ : St × S.Smp → St' × S.Smp) (up : St → S.Msg × Wp → Wp')
      (base : MaskFact (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).J.W → Prop) (Rd : S.Ent → Prop)
      (Rr : S.O → Prop) (own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk]
      (val : Mk → S.Ent → E),
    (∀ x w, m (x, w) = (φ x, (w.1, up x.1 (S.msgs w.1, w.2)))) →
    (∀ st μ μ' wp, S.Alike Rd own μ μ' → up st (μ', wp) = up st (μ, wp)) →
    base ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).wideFact Rd Rr own Mk val) →
    (LdMv.step (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀', Wp', A'⟩ f g m back).After
      base ((⟨S, St', E₀', Wp', A'⟩ : LdStage E Kc).wideFact Rd Rr own Mk val)

/-- A reduction on claims about messages, lifted. -/
def segWide_lift : Prop :=
  ∀ (a : LdStage E Kc) (St' Wp' : Type) (E₀' : ExtSpec) (B : Rels Kc St' E₀' (a.S.Msg × Wp'))
      (R : IOR a.St a.E₀ St' E₀') (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
      (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp) (P : Nums Kc R)
      (base : MaskFact a.J.W → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E),
    (∀ μ μ' wp x c ρ, a.S.Alike Rd own μ μ' →
      ((H.strat (μ', wp) x c).run ρ).1 = ((H.strat (μ, wp) x c).run ρ).1 ∧
      ((H.strat (μ', wp) x c).run ρ).2.1 = ((H.strat (μ, wp) x c).run ρ).2.1 ∧
      ((H.strat (μ', wp) x c).run ρ).2.2.2 = ((H.strat (μ, wp) x c).run ρ).2.2.2) →
    base (a.wideFact Rd Rr own Mk val) →
    (LdMv.sub a ⟨a.S, St', E₀', Wp', B⟩ (.one (a.lift B R H ext P))).After
      base ((⟨a.S, St', E₀', Wp', B⟩ : LdStage E Kc).wideFact Rd Rr own Mk val)

/-- Through "read, then the range check". -/
def ldSegRef_rr_carry : Prop :=
  ∀ (E₀ : ExtSpec) (Wp : Type) (D : LdRrD E Kc E₀ Wp) (base : MaskFact D.s0.J.W → Prop)
      (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop) (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → D.S.Ent → E) (RdN : D.N.Ent → Prop) (RrN : D.N.O → Prop)
      (RdN' : D.N'.Ent → Prop) (RrN' : D.N'.O → Prop),
    D.NoLook Rd own → D.d1.Hyp → D.d3.Hyp → D.d1.NoLook Rd Rr own →
    D.d3.NoLook (D.S.sumP D.N Rd RdN) (D.S.sumO D.N Rr RrN) (D.S.sumP D.N own fun _ => False) →
    base (D.s0.wideFact Rd Rr own Mk val) →
    D.prog.After base
      (D.s4.wideFact ((D.S.sum D.N).sumP D.N' (D.S.sumP D.N Rd RdN) RdN')
        ((D.S.sum D.N).sumO D.N' (D.S.sumO D.N Rr RrN) RrN')
        ((D.S.sum D.N).sumP D.N' (D.S.sumP D.N own fun _ => False) fun _ => False) Mk
        fun M => (D.S.sum D.N).sumV D.N' (D.S.sumV D.N (val M) fun _ => 0) fun _ => 0)

/-- Through the three moves before the digits' lookup. -/
def ldSegRef_dg_carry : Prop :=
  ∀ (E₀ : ExtSpec) (Wp : Type) (Q : LdDgP E Kc E₀ Wp) (mult : Q.X₄ × E → Ms Q.T E₀ → Prop)
      (base : MaskFact Q.D.s4.J.W → Prop) (Rd : Q.T.Ent → Prop) (Rr : Q.T.O → Prop)
      (own : Q.T.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → Q.T.Ent → E),
    base (Q.D.s4.wideFact Rd Rr own Mk val) →
    (Q.pre mult).After base ((Q.lkS mult).wideFact Rd Rr own Mk val)

/-- Through the step that gathers the rows. -/
def ldSegRef_ga_carry : Prop :=
  ∀ (E₀ : ExtSpec) (Wp : Type) (G : LdGaP E Kc E₀ Wp) (St₀ : Type) (g₀ : G.Q.D.St → St₀)
      (Ar : Rels Kc St₀ E₀ (G.Q.T.Msg × Wp)) (base : MaskFact (G.Q.lkT G.ent G.n).J.W → Prop)
      (Rd : G.Q.T.Ent → Prop) (Rr : G.Q.T.O → Prop) (own : G.Q.T.Ent → Prop) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (val : Mk → G.Q.T.Ent → E),
    base ((G.Q.lkT G.ent G.n).wideFact Rd Rr own Mk val) →
    (G.step St₀ g₀ Ar).After base ((G.tgt St₀ Ar).wideFact Rd Rr own Mk val)

end
end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem segWide_keep : Spec.segWide_keep E Kc := by
  intro S St St' Wp Wp' E₀ E₀' A A' f g m back φ up base Rd Rr own Mk _ _ val hm hup hb
  refine segCarry_step (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀', Wp', A'⟩
    f g m back base _ _ _ _ hb fun x w w' M h => ?_
  obtain ⟨al, _, e⟩ := segWide_alike (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) Rd Rr own Mk val w w' M h
  have e' : w'.2 = w.2 := e
  rw [hm, hm]
  refine ⟨rfl, ?_⟩
  have u : up x.1 (S.msgs w'.1, w'.2) = up x.1 (S.msgs w.1, w.2) := by rw [e']; exact hup _ _ _ _ al
  exact Prod.ext (Prod.mk.inj h).1 (Prod.ext (Prod.mk.inj (Prod.mk.inj h).2).1 u)

theorem segWide_lift : Spec.segWide_lift E Kc := by
  intro a St' Wp' E₀' B R H ext P base Rd Rr own Mk _ _ val hH hb
  refine (freshGiven_one (a.lift B R H ext P) base _).2
    (Or.inr ⟨_, (a.wideFact Rd Rr own Mk val).kc, (a.wideFact Rd Rr own Mk val).put, hb, ?_⟩)
  intro w w' M x c ρ h
  obtain ⟨al, _, e⟩ := segWide_alike a Rd Rr own Mk val w w' M h
  have e' : w'.2 = w.2 := e
  have r := hH (a.S.msgs w.1) (a.S.msgs w'.1) w.2 x.1 c ρ al
  have q1 : ((a.lift B R H ext P).H.strat w' x c).run ρ = _ := Sig.liftH_run a.S H w' x c ρ
  have q2 : ((a.lift B R H ext P).H.strat w x c).run ρ = _ := Sig.liftH_run a.S H w x c ρ
  rw [q1, q2, e']
  refine ⟨r.1, ?_, ?_⟩
  · exact Prod.ext r.2.1 rfl
  · exact Prod.ext (Prod.mk.inj h).1 (Prod.ext (Prod.mk.inj (Prod.mk.inj h).2).1 r.2.2)

omit [Field E] [Fintype E] in
/-- alike over two signatures: alike on the first -/
theorem alike_left (S N : Sig E) (Rd own : S.Ent → Prop) (RdN : N.Ent → Prop) (μ μ' : (S.sum N).Msg)
    (h : (S.sum N).Alike (S.sumP N Rd RdN) (S.sumP N own fun _ => False) μ μ') :
    S.Alike Rd own (S.left N (T := OMsg.Msg) μ) (S.left N (T := OMsg.Msg) μ') :=
  fun n hR ho => h ⟨.inl n.1, n.2⟩ hR ho

theorem ldSegRef_rr_carry : Spec.ldSegRef_rr_carry E Kc := by
  intro E₀ Wp D base Rd Rr own Mk _ _ val RdN RrN RdN' RrN' hN h1 h3 n1 n3 hb
  unfold LdRrD.prog
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc,
    LdProg.after_snoc, LdProg.after_nil]
  have f1 := segWide_keep D.S D.St D.St Wp (Wp × D.p.Rds E) E₀ E₀ D.s0.A D.s1.A (fun x => some x)
    (ExtMap.id D.s0.Ex) (readM D.p D.S D.c D.A₀) (fun _ w => (w.1, w.2.1)) id
    (fun st w => (w.2, readsOf (D.c.W st) (D.c.yz (D.A₀.core w))))
    base Rd Rr own Mk val (fun _ _ => rfl) (fun st μ μ' wp al => by
      show (wp, readsOf (D.c.W st) (D.c.yz (D.A₀.core (μ', wp)))) =
        (wp, readsOf (D.c.W st) (D.c.yz (D.A₀.core (μ, wp))))
      rw [hN μ μ' wp al]) hb
  have f2 := segWide_send_old D.s1 D.d1 _ Rd Rr own Mk val RdN RrN h1.sender n1 f1
  have f3 := segWide_lift D.s2 _ _ _ (rngOut D.p D.r D.A₁) (rngDraw D.p D.St E₀)
    (rngDrawH D.p D.r D.A₁) (fun _ _ _ w => w.1) (rngDrawN D.p D.r) _ _ _ _ Mk _
    (fun μ μ' wp x c ρ al => by
      have e : D.r.yz (D.A₁.core (μ', wp)) = D.r.yz (D.A₁.core (μ, wp)) :=
        hN _ _ wp (alike_left D.S D.N Rd own RdN μ μ' al)
      refine ⟨rfl, rfl, ?_⟩
      show (wp, hdig D.p.D D.p.q (D.r.yz (D.A₁.core (μ', wp))) _) =
        (wp, hdig D.p.D D.p.q (D.r.yz (D.A₁.core (μ, wp))) _)
      rw [e]) f2
  have f4 := segWide_keep (D.S.sum D.N) _ _ _ _ E₀ E₀ D.s3.A D.s3v.A (sideF (D.S.sum D.N) id)
    (sideG (D.S.sum D.N) (ExtMap.id E₀)) (sideM (D.S.sum D.N) id fun _ w => (w.2, D.mkV w.2.2))
    (sideB (D.S.sum D.N) fun _ w => w.2.1) (fun x => (x.1, x.2)) (fun _ w => (w.2, D.mkV w.2.2))
    _ _ _ _ Mk _ (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) f3
  exact segWide_send_old D.s3v D.d3 _ _ _ _ Mk _ RdN' RrN' h3.sender n3 f4

theorem ldSegRef_dg_carry : Spec.ldSegRef_dg_carry E Kc := by
  intro E₀ Wp Q mult base Rd Rr own Mk _ _ val hb
  unfold LdDgP.pre
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  have f1 := segWide_keep Q.T _ _ _ _ E₀ E₀ Q.D.s4.A Q.u0.A (sideF Q.T id)
    (sideG Q.T (ExtMap.id E₀)) (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)
    (fun x => (x.1, x.2)) (fun _ w => w.2) base Rd Rr own Mk val (fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl) hb
  have f2 := segWide_lift Q.u0 _ _ _ (Q.sh.jOut Q.R0)
    (IOR.draw E (Prod.mk : Q.X₄ → E → Q.X₄ × E) E₀) (IOR.Honest.draw E Prod.mk E₀ (Q.T.Msg × Wp))
    (fun _ _ _ wp => wp) (IOR.Nums.draw Kc E Prod.mk E₀ (2 ^ (1 + Q.d))) _ Rd Rr own Mk val
    (fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩) f1
  exact segWide_keep Q.T _ _ _ _ E₀ E₀ Q.u1.A (Q.lkS mult).A (sideF Q.T id)
    (sideG Q.T (ExtMap.id E₀)) (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)
    (fun x => (x.1, x.2)) (fun _ w => w.2)
    _ Rd Rr own Mk val (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) f2

theorem ldSegRef_ga_carry :
    Spec.ldSegRef_ga_carry E Kc := fun E₀ _ G St₀ g₀ Ar base Rd Rr own Mk _ _ val hb =>
  segWide_keep G.Q.T _ _ _ _ E₀ E₀ (G.Q.lkT G.ent G.n).A (G.tgt St₀ Ar).A
    (fun x => if x.1.2.2.length = G.n then some (G.fd St₀ g₀ x.1, x.2) else none)
    (sideG G.Q.T (ExtMap.id E₀)) (sideM G.Q.T (G.fd St₀ g₀) fun _ w => w.2)
    (sideB G.Q.T fun _ w => w.2) (fun x => (G.fd St₀ g₀ x.1, x.2)) (fun _ w => w.2)
    base Rd Rr own Mk val (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) hb

end

end Cb
