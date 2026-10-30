-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Count.lean: THE HONEST SIDE THAT LAYS LATE, WITH A COUNTER FOR EACH COPY, which
serves at most s1 sessions on a copy; and what the counting costs.

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean).

lateC is lateW (Johnson/LateWorld/Defs.lean) with a counter for each of the M + 1 places of the
key's list. At a batch of one request of the adversary's own, after the setup, it draws the place j
as the prover does; if the counter of j is below s1 it goes on as lateW and counts j once more; else
it replies with no string, does no hash work, and leaves the table. All other moves are lateW's.

The library's lemma on stopping before a leaf is used too often (Rom/Overrun.lean) is for any two
challengers, and asks its laws AT EVERY STATE of the one that counts. lateC is made so that they
hold at every state: it counts whenever it draws, whether or not the key has a copy at that place.

Main names (namespace OnBytes.LateWorld).
  oneOwn       the call is a batch of one request of the adversary's own, and the setup has been
               made: the key and the instance.
  sessAt       the session at a drawn place: the rest of the prover's coins, then lateAt.
  StC, replyC, lateC   THE CHALLENGER THAT COUNTS: its state, its reply, the challenger.
  lateBatch_one, reply_oneOwn, reply_else   lateW's and lateC's replies, unfolded.
  pairC, lawsC the letters and the laws of Rom/Overrun.lean.
  callBound_of_gAdm   an admissible adversary makes at most n batches.
  late_to_count    lateW and lateC are within Prob.pOver (M + 1) s1 n.
  map_map_id, map_map_eq, oneOwn_some, lateW_reply_oneOwn   small tools.

Limits. s1 is a letter. lateC is a device of the proof and stands in no statement on the scheme.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Defs
import Rom.Overrun

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.GlueB (GCall GIn GAdm)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- a map and a map back -/
theorem map_map_id {α β : Type} (p : PMF α) (f : α → β) (g : β → α) (hg : ∀ a, g (f a) = a) :
    (p.map f).map g = p := by
  rw [PMF.map_comp, show g ∘ f = id from funext hg, PMF.map_id]

/-- two maps, one after the other -/
theorem map_map_eq {α β γ : Type} (p : PMF α) (f : α → β) (g : β → γ) (k : α → γ)
    (hg : ∀ a, g (f a) = k a) : (p.map f).map g = p.map k := by
  rw [PMF.map_comp]
  exact congrArg (fun F => p.map F) (funext hg)

/-- The call is a batch of one request of the adversary's own, and the setup has been made: the key
and the instance. -/
def oneOwn : GCall X Unit → Option (Isk lam L Bd aT aL) → Option (Isk lam L Bd aT aL × X)
  | .batch [(x, _, true)], some k => some (k, x)
  | _, _ => none

theorem oneOwn_some {c : GCall X Unit} {κ : Option (Isk lam L Bd aT aL)}
    {k : Isk lam L Bd aT aL} {x : X} (h : oneOwn c κ = some (k, x)) :
    c = .batch [(x, (), true)] ∧ κ = some k := by
  unfold oneOwn at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, rfl⟩
  · cases h

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- The session at the drawn place j: the rest of the prover's coins, then the prover behind its
coins. -/
def sessAt (k : Isk lam L Bd aT aL) (x : X) (T : Tb W) (j : Fin (h.M + 1)) :
    PMF (RequestProof lam L × Tb W) :=
  (unif (Fin (h.kB.n + 1))).bind fun c => (unif (Fin (h.coB.n + 1))).bind fun e =>
    lateAt W cA r₀ h k x ⟨j.val, h.kB.e c, h.coB.e e⟩ T

/-- lateW's batch of one own request: the place, then the session there. -/
theorem lateBatch_one (k : Isk lam L Bd aT aL) (T : Tb W) (x : X) (u : Unit) :
    lateBatch W cA r₀ h k T [(x, u, true)] =
      (unif (Fin (h.M + 1))).bind fun j =>
        (sessAt W cA r₀ h k x T j).map fun a => ([a.1], a.2) := by
  simp only [lateBatch, coinsP, OComp.runLazy, sessAt, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]

/-- The state of the challenger that counts: lateW's, and a counter for each place of the key's
list. -/
abbrev StC (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (h : HonestSide lam L Bd aT aL) : Type :=
  (Option (Isk lam L Bd aT aL) × Tb W) × (Fin (h.M + 1) → ℕ)

/-- Its reply, by what oneOwn says of the call. -/
def replyC (s1 : ℕ) (i : I) (s : StC W h) (c : GCall X Unit) :
    Option (Isk lam L Bd aT aL × X) → PMF (GIn (FullKey lam L aT aL) (RequestProof lam L) × StC W h)
  | some (k, x) =>
      (unif (Fin (h.M + 1))).bind fun j =>
        if s.2 j < s1 then
          (sessAt W cA r₀ h k x s.1.2 j).map fun a =>
            (.inr [a.1], ((some k, a.2), Function.update s.2 j (s.2 j + 1)))
        else PMF.pure (.inr [⟨j.val, h.nm j.val, none⟩], s)
  | none => ((lateW W S cA r₀ h i).reply s.1 c).map fun a => (a.1, (a.2, s.2))

/-- **THE CHALLENGER THAT COUNTS.** -/
def lateC (s1 : ℕ) (i : I) : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) where
  σ := StC W h
  answer := fun s o q => ((lateW W S cA r₀ h i).answer s.1 o q).map fun a => (a.1, (a.2, s.2))
  reply := fun s c => replyC W S cA r₀ h s1 i s c (oneOwn c s.1.1)

variable {W S cA r₀ h}

theorem reply_else {s1 : ℕ} {i : I} (s : StC W h) (c : GCall X Unit)
    (hc : oneOwn c s.1.1 = none) :
    (lateC W S cA r₀ h s1 i).reply s c =
      ((lateW W S cA r₀ h i).reply s.1 c).map fun a => (a.1, (a.2, s.2)) := by
  show replyC W S cA r₀ h s1 i s c (oneOwn c s.1.1) = _
  rw [hc]
  rfl

theorem reply_oneOwn {s1 : ℕ} {i : I} (k : Isk lam L Bd aT aL) (T : Tb W)
    (ct : Fin (h.M + 1) → ℕ) (x : X) :
    (lateC W S cA r₀ h s1 i).reply ((some k, T), ct) (.batch [(x, (), true)]) =
      (unif (Fin (h.M + 1))).bind fun j =>
        if ct j < s1 then
          (sessAt W cA r₀ h k x T j).map fun a =>
            (.inr [a.1], ((some k, a.2), Function.update ct j (ct j + 1)))
        else PMF.pure (.inr [⟨j.val, h.nm j.val, none⟩], ((some k, T), ct)) := rfl

theorem lateW_reply_oneOwn {i : I} (k : Isk lam L Bd aT aL) (T : Tb W) (x : X) :
    (lateW W S cA r₀ h i).reply (some k, T) (.batch [(x, (), true)]) =
      (unif (Fin (h.M + 1))).bind fun j =>
        (sessAt W cA r₀ h k x T j).map fun a => (.inr [a.1], (some k, a.2)) := by
  show (lateBatch W cA r₀ h k T [(x, (), true)]).map (fun o => (Sum.inr o.1, (some k, o.2))) = _
  rw [lateBatch_one, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

variable (W S cA r₀ h)

/-- The letters of Rom/Overrun.lean: forget the counters; read them. -/
def pairC (s1 : ℕ) (i : I) :
    Overrun.Pair (lateW W S cA r₀ h i) (lateC W S cA r₀ h s1 i) h.M :=
  ⟨fun s => s.1, fun s => s.2⟩

/-- **The laws of Rom/Overrun.lean, at every state.** -/
theorem lawsC (s1 : ℕ) (i : I) :
    Overrun.Laws (pairC W S cA r₀ h s1 i) s1 fun m => ∃ b, m = .batch b where
  answer := fun s o q => by
    show (lateW W S cA r₀ h i).answer s.1 o q =
      (((lateW W S cA r₀ h i).answer s.1 o q).map fun a => (a.1, (a.2, s.2))).map
        (Prod.map id fun s => s.1)
    exact (map_map_id _ _ _ fun _ => rfl).symm
  answer_ctr := fun s o q x hx => by
    have hx' : x ∈ (PMF.map (fun a : _ × (lateW W S cA r₀ h i).σ =>
        ((a.1, (a.2, s.2)) : _ × StC W h)) ((lateW W S cA r₀ h i).answer s.1 o q)).support := hx
    obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx'
    rfl
  reply := fun s m => by
    cases hc : oneOwn m s.1.1 with
    | none =>
      refine Or.inl ⟨?_, fun x hx j => ?_⟩
      · show (lateW W S cA r₀ h i).reply s.1 m = ((lateC W S cA r₀ h s1 i).reply s m).map
          (Prod.map id fun s => s.1)
        rw [reply_else s m hc]
        exact (map_map_id _ _ _ fun _ => rfl).symm
      · rw [reply_else s m hc] at hx
        obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
        exact le_rfl
    | some kx =>
      obtain ⟨k, x⟩ := kx
      obtain ⟨⟨κ, T⟩, ct⟩ := s
      obtain ⟨rfl, hκ⟩ := oneOwn_some hc
      obtain rfl : κ = some k := hκ
      refine Or.inr ⟨⟨_, rfl⟩, PUnit, PMF.pure PUnit.unit,
        fun _ j => (sessAt W cA r₀ h k x T j).map fun a => (.inr [a.1], (some k, a.2)),
        fun _ j =>
          if ct j < s1 then
            (sessAt W cA r₀ h k x T j).map fun a =>
              (.inr [a.1], ((some k, a.2), Function.update ct j (ct j + 1)))
          else PMF.pure (.inr [⟨j.val, h.nm j.val, none⟩], ((some k, T), ct)), ?_, ?_, ?_⟩
      · rw [PMF.pure_bind]
        exact lateW_reply_oneOwn k T x
      · rw [PMF.pure_bind]
        exact reply_oneOwn k T ct x
      · intro _ j hj
        have hj' : ct j < s1 := hj
        refine ⟨?_, fun y hy => ?_⟩
        · simp only [if_pos hj']
          refine (map_map_eq _ _ _ _ ?_).symm
          intro _
          rfl
        · simp only [if_pos hj'] at hy
          obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
          rfl

/-- An admissible adversary makes at most n batches. -/
theorem callBound_of_gAdm {Sp : OSpec} {IVK Pf α : Type} {ok : ZKCP.Gen.Batch X Unit → Prop}
    (A : Adv Sp (GCall X Unit) (GIn IVK Pf) α) :
    ∀ (f : Bool) (n : ℕ), GAdm ok A f n → A.CallBound (fun m => ∃ b, m = .batch b) n := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun f n hA r => ih r f n (hA r)
  | query o q k ih => exact fun f n hA r => ih r f n (hA r)
  | call c k ih =>
    intro f n hA
    rcases c with _ | b
    · obtain ⟨-, hk⟩ := hA
      exact ⟨fun ⟨b, e⟩ => (by cases e), fun _ a => ih a true n (hk a)⟩
    · cases n with
      | zero => exact hA.elim
      | succ n =>
        obtain ⟨-, -, hk⟩ := hA
        exact ⟨fun _ => ⟨n, rfl, fun a => ih a f n (hk a)⟩, fun hn => absurd ⟨b, rfl⟩ hn⟩

/-- **What the counting costs.** -/
theorem late_to_count (s1 : ℕ) (i : I) {α : Type} {ok : ZKCP.Gen.Batch X Unit → Prop}
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (f : Bool) (n : ℕ) (hA : GAdm ok A f n)
    (s : (lateW W S cA r₀ h i).σ) :
    tv ((interact (lateW W S cA r₀ h i) A s).map Prod.fst)
        ((interact (lateC W S cA r₀ h s1 i) A (s, fun _ => 0)).map Prod.fst) ≤
      Prob.pOver (h.M + 1) s1 n :=
  Overrun.tv_le_pOver (lawsC W S cA r₀ h s1 i) A n (s, fun _ => 0) rfl
    (callBound_of_gAdm A f n hA)

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.lawsC
#print axioms OnBytes.LateWorld.late_to_count
