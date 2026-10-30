-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Cut.lean: how the data of a compiled verifier's chain over a shape `s ++ u` split
into the data over s and over u, and the law of the chain itself.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The library has these cuts for transcripts, verifier messages, plain parts and positions
(`Tr.fst`, `Rho.fst`, Iop/Shape.lean; `Plains.fst`, `OPos.left`, Iop/ShapeKit.lean) and joins two
annotations (`RoundSplits.app`, Iop/Batch.lean). Here are the same for what the compiler adds: the wire
records of the rounds, the plain part of one component, and the roots that a chain has taken.

Main names:
  `WireSB.fst`, `WireSB.snd`, `WireSB.app`: the wire records of the rounds of s, of u, of both;
    `WireSB.okg_iff`, `WireSB.ok_iff`, `WireSB.depthLe_iff`: their laws hold of both halves.
  `PB.left`, `PB.right`: the plain part of a component of a round of s, or of u, as one of `s ++ u`.
  `RT.app`, `RT.fst`, `RT.snd`, `RT.count_app`: the roots round by round.
  `thenO`: run an algorithm that may yield none, and go on if it yields a value; its laws.
  `chainB_app`: the chain over `s ++ u` is the chain over s and then the chain over u, which begins
    in the phase in which the first has ended, with the roots that the first has left, and counts
    its rounds on from `i + s.length`.

Limits: nothing here speaks of what follows the chain (the checks of openings), of a protocol or of
soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Iop.ShapeKit
import Rom.Bridge

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The wire records of the rounds -/

/-- the wire records of the rounds of s -/
def WireSB.fst : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} →
    RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B) → RoundsQueryLayout lam K s A
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, _), _, (w, W) => (w, WireSB.fst W)

/-- the wire records of the rounds of u -/
def WireSB.snd : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} →
    RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B) → RoundsQueryLayout lam K u B
  | [], _, _, _, W => W
  | _ :: _, _, (_, _), _, (_, W) => WireSB.snd W

/-- the wire records of the rounds of s, then those of u -/
def WireSB.app : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} →
    RoundsQueryLayout lam K s A → RoundsQueryLayout lam K u B → RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)
  | [], _, _, _, _, V => V
  | _ :: _, _, (_, _), _, (w, W), V => (w, WireSB.app W V)

theorem WireSB.app_fst_snd : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)), WireSB.app (WireSB.fst W) (WireSB.snd W) = W
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (w, W) => congrArg (Prod.mk w) (WireSB.app_fst_snd W)

theorem WireSB.fst_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B), WireSB.fst (WireSB.app W V) = W
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (w, W), V => congrArg (Prod.mk w) (WireSB.fst_app W V)

theorem WireSB.snd_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B), WireSB.snd (WireSB.app W V) = V
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (_, W), V => WireSB.snd_app W V

/-- the wire records over `s ++ u` are lawful exactly if those over s and those over u are -/
theorem WireSB.okg_iff : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)),
    RoundsQueryLayout.OKG (s ++ u) (RoundSplits.app A B) W ↔
      RoundsQueryLayout.OKG s A (WireSB.fst W) ∧ RoundsQueryLayout.OKG u B (WireSB.snd W)
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, _), _, (_, W) =>
    (and_congr_right fun _ => WireSB.okg_iff W).trans and_assoc.symm

theorem WireSB.ok_iff : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)),
    RoundsQueryLayout.OK (s ++ u) (RoundSplits.app A B) W ↔
      RoundsQueryLayout.OK s A (WireSB.fst W) ∧ RoundsQueryLayout.OK u B (WireSB.snd W)
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, _), _, (_, W) =>
    (and_congr_right fun _ => WireSB.ok_iff W).trans and_assoc.symm

/-- no tree over `s ++ u` is deeper than d exactly if none over s and none over u is -/
theorem WireSB.depthLe_iff (d : ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)),
    RoundsQueryLayout.DepthLe d (s ++ u) (RoundSplits.app A B) W ↔
      RoundsQueryLayout.DepthLe d s A (WireSB.fst W) ∧ RoundsQueryLayout.DepthLe d u B (WireSB.snd W)
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, _), _, (_, W) =>
    (and_congr_right fun _ => WireSB.depthLe_iff d W).trans and_assoc.symm

/-! ## The plain part of one component -/

/-- the plain part of a component of a round of s, as one of `s ++ u` -/
def PB.left : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} → PlainPart s A → PlainPart (s ++ u) (RoundSplits.app A B)
  | [], _, _, _, z => nomatch z
  | _ :: _, _, (_, _), _, .inl z => .inl z
  | _ :: _, _, (_, _), _, .inr z => .inr (PB.left z)

/-- the plain part of a component of a round of u, as one of `s ++ u` -/
def PB.right : {s u : Shape} → {A : RoundSplits s} → {B : RoundSplits u} → PlainPart u B → PlainPart (s ++ u) (RoundSplits.app A B)
  | [], _, _, _, z => z
  | _ :: _, _, (_, _), _, z => .inr (PB.right z)

/-! ## The roots that a chain has taken, round by round -/

def RT.app : {s u : Shape} → RootsOfChain lam s → RootsOfChain lam u → RootsOfChain lam (s ++ u)
  | [], _, _, R' => R'
  | _ :: _, _, (c, R), R' => (c, RT.app R R')

def RT.fst : {s u : Shape} → RootsOfChain lam (s ++ u) → RootsOfChain lam s
  | [], _, _ => ()
  | _ :: _, _, (c, R) => (c, RT.fst R)

def RT.snd : {s u : Shape} → RootsOfChain lam (s ++ u) → RootsOfChain lam u
  | [], _, R => R
  | _ :: _, _, (_, R) => RT.snd R

theorem RT.app_fst_snd : ∀ {s u : Shape} (R : RootsOfChain lam (s ++ u)),
    RT.app (RT.fst R) (RT.snd (s := s) R) = R
  | [], _, _ => rfl
  | _ :: _, _, (c, R) => congrArg (Prod.mk c) (RT.app_fst_snd R)

theorem RT.fst_app : ∀ {s u : Shape} (R : RootsOfChain lam s) (R' : RootsOfChain lam u), RT.fst (RT.app R R') = R
  | [], _, _, _ => rfl
  | _ :: _, _, (c, R), R' => congrArg (Prod.mk c) (RT.fst_app R R')

theorem RT.snd_app : ∀ {s u : Shape} (R : RootsOfChain lam s) (R' : RootsOfChain lam u),
    RT.snd (s := s) (RT.app R R') = R'
  | [], _, _, _ => rfl
  | _ :: _, _, (_, R), R' => RT.snd_app R R'

/-- the roots taken over `s ++ u` are those taken over s and those taken over u -/
theorem RT.count_app : ∀ {s u : Shape} (R : RootsOfChain lam s) (R' : RootsOfChain lam u),
    RootsOfChain.count (s ++ u) (RT.app R R') = RootsOfChain.count s R + RootsOfChain.count u R'
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (c, R), R' => by
    have h := RT.count_app R R'
    show _ + _ + RootsOfChain.count _ (RT.app R R') = _ + _ + RootsOfChain.count _ R + _
    omega

/-! ## The chain -/

/-- run c; if it yields a value, go on with g; if it yields none, stop with none -/
def thenO {α β : Type} (c : TypedOracleComputation lam K L (Option α)) (g : α → TypedOracleComputation lam K L (Option β)) :
    TypedOracleComputation lam K L (Option β) :=
  c.bind fun r => match r with
    | none => OComp.pure none
    | some a => g a

theorem thenO_pure_some {α β : Type} (a : α) (g : α → TypedOracleComputation lam K L (Option β)) :
    thenO (OComp.pure (some a)) g = g a := rfl

theorem thenO_pure_none {α β : Type} (g : α → TypedOracleComputation lam K L (Option β)) :
    thenO (OComp.pure none) g = OComp.pure none := rfl

theorem thenO_query {α β : Type} (o : OracleName) (q : domOf lam L o)
    (k : rngOf lam K o → TypedOracleComputation lam K L (Option α)) (g : α → TypedOracleComputation lam K L (Option β)) :
    thenO (OComp.query (S := typedOracleFamily lam K L) o q k) g =
      OComp.query (S := typedOracleFamily lam K L) o q fun r => thenO (k r) g := rfl

theorem thenO_assoc {α β γ : Type} (c : TypedOracleComputation lam K L (Option α)) (g : α → TypedOracleComputation lam K L (Option β))
    (h : β → TypedOracleComputation lam K L (Option γ)) :
    thenO (thenO c g) h = thenO c fun a => thenO (g a) h := by
  unfold thenO
  rw [OComp.bind_assoc]
  congr 1
  funext r
  cases r <;> rfl

/-- to go on with nothing but the value itself changes nothing -/
theorem thenO_pure {α : Type} (c : TypedOracleComputation lam K L (Option α)) :
    thenO c (fun a => OComp.pure (some a)) = c := by
  unfold thenO
  induction c with
  | pure r => cases r <;> rfl
  | query o q k ih => exact congrArg (OComp.query o q) (funext ih)
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)

/-- the form in which `recomputeChain` lays a round's data before the later rounds' -/
theorem bind_map_eq_thenO {α β : Type} (c : TypedOracleComputation lam K L (Option α)) (f : α → β) :
    (c.bind fun r => OComp.pure (r.map f)) = thenO c fun a => OComp.pure (some (f a)) := by
  unfold thenO
  congr 1
  funext r
  cases r <;> rfl

/-- what `takeRt` leaves, and how many roots it takes -/
theorem takeRt_some {n : ℕ} {rts a b : List (Dig lam)} (h : takeRt n rts = some (a, b)) :
    a.length = n ∧ b = rts.drop n := by
  unfold takeRt at h
  split at h
  · rename_i hn
    cases h
    exact ⟨List.length_take_of_le hn.2, rfl⟩
  · cases h

/-- **The chain over `s ++ u`** is the chain over s, then the chain over u from the phase and the
roots that the first has left, its rounds counted on from `i + s.length`. -/
theorem chainB_app (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s u : Shape) (A : RoundSplits s) (B : RoundSplits u) (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
      (embP : PlainPart (s ++ u) (RoundSplits.app A B) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (s ++ u)),
      recomputeChain t cms x salt rtreq (s ++ u) (RoundSplits.app A B) W embP i ph rts pls =
        thenO (recomputeChain t cms x salt rtreq s A (WireSB.fst W) (fun z => embP (PB.left z)) i ph rts
          (Plains.fst pls)) fun a =>
        thenO (recomputeChain t cms x salt rtreq u B (WireSB.snd W) (fun z => embP (PB.right z))
          (i + s.length) a.2.2 (rts.drop (RootsOfChain.count s a.2.1)) (Plains.snd pls)) fun b =>
        OComp.pure (some (Rho.app a.1 b.1, RT.app a.2.1 b.2.1, b.2.2))
  | [], u, _, B, W, embP, i, ph, rts, pls =>
    (thenO_pure (recomputeChain t cms x salt rtreq u B W embP i ph rts pls)).symm
  | r :: s, u, (a, A), B, (w, W), embP, i, ph, rts, (pl, pls) => by
    have ih := fun embP' i' ph' rts' =>
      chainB_app t cms x salt rtreq s u A B W embP' i' ph' rts' pls
    have hi : i + (r :: s).length = i + 1 + s.length := by
      rw [List.length_cons]; omega
    show recomputeChain t cms x salt rtreq (r :: (s ++ u)) (a, RoundSplits.app A B) (w, W) embP i ph rts
        (pl, pls) =
      thenO (recomputeChain t cms x salt rtreq (r :: s) (a, A) (w, WireSB.fst W)
        (fun z => embP (PB.left z)) i ph rts (pl, Plains.fst pls)) _
    rw [hi]
    have tail : ∀ (c : RtC lam × RtC lam) (ch : r.Chal) (ph1 : Phase lam) (rts' : List (Dig lam)),
        rts' = rts.drop ((c.1.getD []).length + (c.2.getD []).length) →
        ((recomputeChain t cms x salt rtreq (s ++ u) (RoundSplits.app A B) W (fun z => embP (Sum.inr z)) (i + 1)
            ph1 rts' pls).bind fun r1 =>
          OComp.pure (r1.map fun z =>
            (((ch, z.1), (c, z.2.1), z.2.2) :
              Rho (r :: (s ++ u)) × RootsOfChain lam (r :: (s ++ u)) × Phase lam))) =
        thenO ((recomputeChain t cms x salt rtreq s A (WireSB.fst W)
            (fun z => embP (PB.left (s := r :: s) (A := (a, A)) (Sum.inr z))) (i + 1) ph1 rts'
            (Plains.fst pls)).bind fun r1 =>
          OComp.pure (r1.map fun z =>
            (((ch, z.1), (c, z.2.1), z.2.2) : Rho (r :: s) × RootsOfChain lam (r :: s) × Phase lam)))
          fun a1 =>
          thenO (recomputeChain t cms x salt rtreq u B (WireSB.snd (s := r :: s) (A := (a, A)) (w, W))
            (fun z => embP (PB.right z)) (i + 1 + s.length) a1.2.2
            (rts.drop (RootsOfChain.count (r :: s) a1.2.1)) (Plains.snd (s := r :: s) (pl, pls))) fun b =>
          OComp.pure (some (Rho.app a1.1 b.1, RT.app a1.2.1 b.2.1, b.2.2)) := by
      intro c ch ph1 rts' hd
      rw [ih, bind_map_eq_thenO, bind_map_eq_thenO, thenO_assoc, thenO_assoc]
      congr 1
      funext a'
      rw [thenO_assoc, thenO_pure_some]
      have e : rts'.drop (RootsOfChain.count s a'.2.1) = rts.drop (RootsOfChain.count (r :: s) (c, a'.2.1)) := by
        rw [hd, List.drop_drop]
        rfl
      rw [e]
      rfl
    simp only [recomputeChain]
    generalize actOf cms (Option.map L.early x) salt a.kind ph = act
    rcases act with _ | ⟨h, _ | _, next⟩ | ρ
    · rfl
    · dsimp only
      generalize h0 : takeRt w.depth0.length rts = tk
      rcases tk with _ | ⟨rt, rts'⟩
      · rfl
      · obtain ⟨h1, h2⟩ := takeRt_some h0
        refine congrArg (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) _) (funext fun ans => ?_)
        exact tail (some rt, none) (w.chal ans.1) _ rts' (by rw [h2]; simp [h1])
    · dsimp only
      generalize hJ : takeRt w.depthJ.length rts = tk
      rcases tk with _ | ⟨rt, rts'⟩
      · rfl
      · obtain ⟨h1, h2⟩ := takeRt_some hJ
        refine congrArg (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) _) (funext fun ans => ?_)
        exact tail (none, some rt) (w.chal ans.1) _ rts' (by rw [h2]; simp [h1])
    · dsimp only
      generalize hJ : takeRt w.depthJ.length rts = tk
      rcases tk with _ | ⟨rtj, rts1⟩
      · rfl
      · dsimp only
        generalize h0 : takeRt w.depth0.length rts1 = tk0
        rcases tk0 with _ | ⟨rt0, rts'⟩
        · rfl
        · obtain ⟨h1, h2⟩ := takeRt_some hJ
          obtain ⟨h3, h4⟩ := takeRt_some h0
          refine congrArg (OComp.query (S := typedOracleFamily lam K L) (OracleName.g t) _) (funext fun c => ?_)
          refine congrArg (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) _) (funext fun ans => ?_)
          exact tail (some rt0, some rtj) (w.chal ans.1) _ rts'
            (by rw [h4, h2, List.drop_drop]; simp [h1, h3, Nat.add_comm])

end TypedOracleCompiler.Joined
