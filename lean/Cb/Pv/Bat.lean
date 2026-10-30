-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Bat.lean: the round before a proximity test's first fold, as one kind of block: the
reduction, its joints, the statement that it is knowledge sound, and what is proved beside it.

A proximity test on a group of oracle messages begins with one round in which the prover sends
nothing and the verifier draws the seed of coefficients: all open rows on the group and the sample
rows of all its members become one row. The reduction is the library's `ldBridge`
(Cb/Ld/LdBatSig.lean): a step without rounds, in which the sample rows join the claim's rows and
what is kept for later is set beside, and the draw. Nothing of it is stated anew. The file imports
no file of the program.

  `Size`      what is public of such a round: the family S of oracle messages; the group G (its
              members, the common long positions, the joint radius); which members are kept (keep);
              the names B, states Sb and forms sl of the open rows; the coefficients Z, one for each
              open row and each sample row; a bound L on the lists of the group's code at the joint
              radius. Data alone: no field is a proof. `kp`: the kept messages are those outside the
              group and the members marked, so that every message is a member or kept (`hc`).
  `R`, `eps`  the reduction, one round; its error L * Z.err, a count of seeds.
  `inJ`       the joint before: the rows hold of the group's message, beside a joint A₀ on the kept
              messages; relaxed by decoding with a sample; on statements without a collision.
  `outJ`      the joint after: the group's word is within the joint radius of a code word whose
              message meets the one combined row, beside A₀ on the kept messages.
  `HAt s`     the statement at the size s. Bound inside: the types of cores, of the carried
              statement and of the further witness, the further oracles, and A₀. It says: the
              reduction is knowledge sound (`Reduction.Know`) on the statements of `inJ`, between
              the two relaxed relations, with the library's extractor `ldBrBack`, at `eps s`. The
              round changes the type of the witness (from pairs for each message to one pair for the
              group's code, beside the kept ones), so there is no tuple of messages that stays
              fixed, and the statement has none.
  `hAt`       the statement holds if the coefficients evade zero (Z.OK), the lists are bounded by L,
              and the joint radius implies each member's own (G.Fits): the library's `ldBat_bridge`.
  `hAtCf`     the same between the two joints with their conditions moved into the relaxed
              relations: `know_bridge` (Cb/Ent/CloseKnowProofs.lean).
  `send_bat_seam`   the output joint of a sending (Cb/Pv/Send.lean) of the round's whole family, at
              the round's base joint, is this round's input joint in that second form.
  Beside it: `point`, `isLocal`, `passes`, `never_rejects`, `rounds`, `errs`, `vals` for all sizes;
  `onOut` under the three conditions.
  `powersZ`, `powersZ_ok`   the powers of one element as coefficients, at rows that are numbered
              below n without repeats (meant as the program's; not compared here); they evade zero
              (`ok_powers_comap`, Cb/Ent/CloseKnowProofs.lean); the evader's error count is n - 1,
              of as many seeds as the field has elements.
  `HNum E rows list`, `hNum`   the statement with these coefficients, by two public numbers alone:
              for every group whose rows are numbered below `rows` without repeats, whose lists are
              bounded by `list` and whose radius fits: knowledge sound at the error list * (rows -
              1). Proved for all numbers.

Not shown here. That a group of a key file's chains has bounded lists or a radius that fits. That
the error is a plan's bound. That the powers of one element are the program's coefficients. Anything
on an honest prover.
Limits: how the output joint meets the input joint of a test's first fold (Cb/Pv/Tower/Fold.lean,
Cb/Pv/Tower/Stage.lean) is not laid here: between them stand the arrangement of the rows and the cut
of the form, beside the kept part (Cb/Pv/Tower/First.lean: `batFoldOwn`,
`batFoldRide`). The error is a bare count for one instance: nothing on proof of work, nothing on
several instances.

-/
import Cb.Ld.LdBatSigProofs
import Cb.Ld.LdLinProofsChain
import Cb.Gen.BatEvaderProofs
import Cb.Ld.LdWfPre
import Ior.KnowCollRulesChainErr
import Cb.Ent.CloseKnowProofs
import Cb.Pv.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Bat
open Iop IOR Prob Cb

/-- What is public of the round. -/
structure Size (E : Type) [Field E] [Fintype E] where
  S : Sig E
  G : Grp S
  /-- the members of the group that are kept for later -/
  keep : S.O → Prop
  [decKeep : DecidablePred keep]
  B : Type
  [finB : Fintype B]
  Sb : B → Type
  sl : ∀ b, Slf E (Sb b) G.C.J
  Z : Evader E (G.Row B)
  L : ℕ

attribute [instance] Size.decKeep Size.finB

/-- The messages that are kept: all that are no members of the group, and the members marked. -/
def Size.kp {E : Type} [Field E] [Fintype E] (s : Size E) : s.S.O → Prop :=
  fun o => ¬ s.G.mem o ∨ s.keep o

instance {E : Type} [Field E] [Fintype E] (s : Size E) : DecidablePred s.kp :=
  fun o => inferInstanceAs (Decidable (¬ s.G.mem o ∨ s.keep o))

/-- Every message is a member of the group or kept. -/
theorem Size.hc {E : Type} [Field E] [Fintype E] (s : Size E) : ∀ o, s.G.mem o ∨ s.kp o :=
  fun o => (Decidable.em (s.G.mem o)).elim Or.inl fun h => Or.inr (Or.inl h)

section
variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The reduction. -/
noncomputable def R (St₀ : Type) (E₀ : ExtSpec) :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (E₀.prod s.S.ext)
      (LdBrXo s.G s.kp s.Sb s.Z St₀) (LdBrE s.G s.kp E₀) :=
  ldBridge s.G s.kp s.Sb s.Z St₀ E₀

/-- The error. -/
def eps : ℕ × Unit := (s.L * s.Z.err, ())

variable {Kc St₀ Wp : Type} {E₀ : ExtSpec}

/-- The joint before the round. -/
def inJ (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    Rels Kc ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (E₀.prod s.S.ext) (s.S.Wit × Wp) :=
  s.S.over (claimRels (fun x m => Slf.All s.sl x (s.G.msg m))
    (onMsgRels (s.S.res (T := OMsg.Msg) s.kp) A₀))

/-- The joint after the round. -/
def outJ (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    Rels Kc (LdBrXo s.G s.kp s.Sb s.Z St₀) (LdBrE s.G s.kp E₀) (LdBrW s.G s.kp Wp) :=
  IOR.Rels.beside (s.G.C.rels (Slf.bat s.Z.ze (s.G.rows s.sl)) s.G.e fun _ => ())
    ((s.S.sub s.kp).over A₀)

end

/-- The statement that the round at the size s is knowledge sound. -/
def HAt {E : Type} [Field E] [Fintype E] (s : Size E) : Prop :=
  ∀ (Kc St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)),
    (R s St₀ E₀).red.Know (inJ s A₀).on (inJ s A₀).relR (outJ s A₀).relR
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (eps s)

section
variable {E : Type} [Field E] [Fintype E] (s : Size E)

/-- The library's statement on the bridge, at budgets that ask nothing. -/
private theorem piece (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits)
    (Kc St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    PieceTr (ldBridge s.G s.kp s.Sb s.Z St₀ E₀) (ldBridgeH s.G s.kp s.Sb s.Z St₀ Wp E₀)
      (inJ s A₀) (outJ s A₀) (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
      (ldBridgeN s.G s.kp s.Sb s.Z St₀ E₀ Kc (s.L * s.Z.err)) (fun _ => True) (fun _ => True) :=
  ldBat_bridge E s.B Kc St₀ Wp s.S s.G s.kp s.Sb s.sl s.Z s.L E₀ A₀ s.hc (fun _ => True)
    (fun _ => True) hZ hL hF fun _ _ => trivial

/-- The statement holds if the coefficients evade zero, the lists are bounded, the radius fits. -/
theorem hAt (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) : HAt s :=
  fun Kc St₀ Wp E₀ A₀ => (piece s hZ hL hF Kc St₀ Wp E₀ A₀).good.know

/-- The same, with the joints' conditions moved into the relaxed relations. -/
theorem hAtCf (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) (Kc St₀ Wp : Type)
    (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    (R s St₀ E₀).red.Know (inJ s A₀).cf.on (inJ s A₀).cf.relR (outJ s A₀).cf.relR
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (eps s) :=
  know_bridge E s.B Kc St₀ Wp s.S s.G s.kp s.Sb s.sl E₀ A₀ s.hc s.Z s.L hZ hL hF

/-- The seam from a sending of the round's whole family to the round: one joint. -/
theorem send_bat_seam (Sd : s.S.Seeds) (L : s.S.O → ℕ) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    Send.outJ (⟨s.S, Sd, L⟩ : Send.Size E)
        (claimRels (fun x m => Slf.All s.sl x (s.G.msg m))
          (onMsgRels (s.S.res (T := OMsg.Msg) s.kp) A₀)) Prod.mk =
      (inJ s A₀).cf := rfl

/-! ### beside the statement -/

theorem point (St₀ : Type) (E₀ : ExtSpec) : Nonempty (R s St₀ E₀).shape.IsPoint :=
  ⟨((Blocks.plainPoint Unit s.Z.D (), ()) : (drawRound s.Z.D).IsPoint × Unit)⟩

/-- A draw reads nothing. -/
private theorem draw_isLocal {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X')
    (Ex : ExtSpec) : (IOR.draw D nx Ex).IsLocal :=
  (piece_draw Unit X X' Ex Unit D nx
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ 0 (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ => rfl)
    (fun _ _ _ => le_of_eq (cnt_false fun _ h => h.elim fun _ h' => h'.2 trivial))).good.isLocal

theorem isLocal (St₀ : Type) (E₀ : ExtSpec) : (R s St₀ E₀).IsLocal := by
  obtain ⟨_, hfs, _, hcomp, hpair⟩ := extMap_isLocal
  exact (draw_isLocal s.Z.D _ _).pre _ _
    (hpair _ _ _ _ _ (hcomp _ _ _ _ _ s.G.toExt_isLocal (hfs E₀ s.S.ext).2)
      (hpair _ _ _ _ _ (hfs E₀ s.S.ext).1
        (hcomp _ _ _ _ _ (Sig.subExt_isLocal s.kp) (hfs E₀ s.S.ext).2)))

theorem onOut (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) {Kc St₀ Wp : Type}
    {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) :
    ∀ a τ b, (inJ s A₀).on a → (R s St₀ E₀).red.out a τ = some b → (outJ s A₀).on b :=
  (piece s hZ hL hF Kc St₀ Wp E₀ A₀).good.onOut

/-- The carried statement is handed on. -/
theorem passes (St₀ : Type) (E₀ : ExtSpec) :
    (R s St₀ E₀).Passes (fun x => x.1.2) (fun x' => x'.2.1) := by
  intro x y τ x' h
  have h' : some (ldBrNx s.G s.kp s.Sb s.Z St₀ (ldBrF s.G s.kp s.Sb St₀ x) (drawn τ)) = some x' := h
  rw [← Option.some.inj h']
  rfl

/-- The verifier never rejects. -/
theorem never_rejects (St₀ : Type) (E₀ : ExtSpec)
    (x : (((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (y : (E₀.prod s.S.ext).Str)
    (τ : Tr (R s St₀ E₀).shape) : ((R s St₀ E₀).out x y τ).isSome := rfl

theorem rounds (St₀ : Type) (E₀ : ExtSpec) : (R s St₀ E₀).shape.length = 1 := rfl

theorem errs (St₀ : Type) (E₀ : ExtSpec) :
    Err.toList (s := (R s St₀ E₀).shape) (eps s) = [s.L * s.Z.err] := rfl

theorem vals (St₀ : Type) (E₀ : ExtSpec) :
    (R s St₀ E₀).shape.chalList = [Fintype.card s.Z.D] := rfl

end

/-! ### the powers of one element as coefficients -/

section
variable {E : Type} [Field E] [Fintype E]

/-- The powers of one element, at rows that are numbered below n. -/
@[reducible] def powersZ {J : Type} (n : ℕ) (f : J → Fin n) : Evader E J :=
  (Evader.powers E n).comap f

theorem powersZ_ok {J : Type} [Fintype J] (n : ℕ) (f : J → Fin n) (hf : Function.Injective f) :
    (powersZ (E := E) n f).OK :=
  ok_powers_comap E J n f hf

end

/-- The statement with these coefficients, by two public numbers. -/
def HNum (E : Type) [Field E] [Fintype E] (rows list : ℕ) : Prop :=
  ∀ s : Size E, ∀ f : s.G.Row s.B → Fin rows, Function.Injective f → s.Z = powersZ rows f →
    s.L = list → s.G.C.ListAt s.G.e list → s.G.Fits →
    ∀ (Kc St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)),
      (R s St₀ E₀).red.Know (inJ s A₀).on (inJ s A₀).relR (outJ s A₀).relR
        (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) ((list * (rows - 1), ()) : ℕ × Unit)

theorem hNum (E : Type) [Field E] [Fintype E] (rows list : ℕ) : HNum E rows list := by
  intro s f hf hZ hLe hL hF Kc St₀ Wp E₀ A₀
  have h := hAt s (by rw [hZ]; exact powersZ_ok rows f hf) (by rw [hLe]; exact hL) hF Kc St₀ Wp
    E₀ A₀
  have e : eps s = ((list * (rows - 1), ()) : ℕ × Unit) := by
    unfold eps
    rw [hLe, hZ]
  rw [e] at h
  exact h

#print axioms hAt
#print axioms hAtCf
#print axioms hNum
#print axioms isLocal

end Cb.Pv.Bat
