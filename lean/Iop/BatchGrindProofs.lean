-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchGrindProofs.lean: rounds with proof-of-work bits in a protocol with slots (`BatchInteractiveOracleProof`,
Iop/Batch.lean): the proofs of the statements of Iop/BatchGrind.lean, whose header says what they do
and do not say. Auxiliary lemmas are in the namespace `Iop.BatchGrind`. Stripping drops nonces and
proof-of-work bits. (Words of this library: lean/GLOSSARY.md.)
On soundness: `SndB`, `SndBL` and `BatchProtocol.SoundAt` are preserved, for every list g, with the lists of
errors `Err.grind g ε` (`sndB_grind`, `sndBL_grind`, `BatchProtocol.SoundAt.grind`). `grindSoundB`:
`BatchProtocol.Sound` at εs' from explicit error lists (statement and hypotheses: Iop/BatchGrind.lean).
The state function (section 3): `gst g fl S t` = fl, and all proof-of-work bits in t are 0, and S of
the stripped t. The flag fl says whether all such bits of the earlier rounds were 0. It is the state
function of ethSTARK's Theorem 6 in the form for all rounds: after a failed test the state stays 0
for good. (A failed test: a proof-of-work bit that is 1.)
After the pattern of Iop/BatchPullProofs.lean, some of whose auxiliary lemmas are used.
-/
import Iop.BatchGrind
import Iop.GrindProofs
import Iop.BatchPullProofs

namespace Iop
open Prob
open scoped ENNReal

namespace BatchGrind
open BatchPull (slot_mapAll shOf_map loOf_map slotOut output_eq)

variable {W : Type} [Inhabited W]

/-! ## 1. Challenges -/

theorem slot_strip {N : ℕ} (j : Fin N) :
    ∀ {s : Shape} (g : GBits s) {A : RoundSplits s} (ρ : BRho N (s.grind W g) (A.grind W g)),
      (BRho.strip g ρ).slot j = Rho.strip g (ρ.slot j)
  | [], _, _, _ => rfl
  | _ :: _, (_, g), (a, _), (v, ρ) => Prod.ext (slot_mapAll GChal.old j a.kind v) (slot_strip j g ρ)

theorem lo_strip :
    ∀ {s : Shape} (g : GBits s) (A : RoundSplits s) (ρ : Rho (s.grind W g)),
      RhoLo.strip g (Rho.lo (A.grind W g) ρ) = Rho.lo A (Rho.strip g ρ)
  | [], _, _, _ => rfl
  | _ :: _, (_, g), (a, A), (c, ρ) => Prod.ext (loOf_map GChal.old a.kind c) (lo_strip g A ρ)

theorem sh_strip :
    ∀ {s : Shape} (g : GBits s) (A : RoundSplits s) (ρ : Rho (s.grind W g)),
      RhoSh.strip g (Rho.sh (A.grind W g) ρ) = Rho.sh A (Rho.strip g ρ)
  | [], _, _, _ => rfl
  | _ :: _, (_, g), (a, A), (c, ρ) => Prod.ext (shOf_map GChal.old a.kind c) (sh_strip g A ρ)


/-! ## 2. Annotations -/

/-- The stripped message of two components is the message of the stripped components. -/
theorem strip_join {r : Round} (a : RAnn r) :
    ∀ (b : ℕ) (m0 : (a.grind W b).M0) (mj : (a.grind W b).Mj),
      Round.stripMsg ((a.grind W b).join m0 mj) = a.join (GPlain.old m0) (GPlain.old mj) := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
  intro b
  cases b with
  | zero => intro _ _; rfl
  | succ b =>
    cases k
    · rintro ⟨_, _⟩ _; rfl
    · rintro _ ⟨_, _⟩; rfl

/-- The message of two components with the same nonce ν, of which one is dropped, is the old message
with the nonce ν. -/
theorem join_mk {r : Round} (a : RAnn r) :
    ∀ (b : ℕ) (m0 : a.M0) (mj : a.Mj) (ν : W),
      (a.grind W b).join (GPlain.mk (a.kind.b0 b) m0 ν) (GPlain.mk (a.kind.bJ b) mj ν) =
        Round.fillMsg b (a.join m0 mj) ν := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
  intro b
  cases b with
  | zero => intro _ _ _; rfl
  | succ b => cases k <;> (intro _ _ _; rfl)

theorem coherent_round {r : Round} {a : RAnn r} (h : a.Coherent) (b : ℕ) :
    (a.grind W b).Coherent := by
  refine ⟨?_, fun m0 mj mj' p hp => ?_, fun m0 m0' mj p hp => ?_⟩
  · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
    cases b with
    | zero => exact h.plain_join
    | succ b =>
      cases k
      · rintro ⟨m0, ν⟩ mj
        have e : pl (sp.symm (m0, mj)).2 = (pl0 m0, plj mj) := h.plain_join m0 mj
        show (((pl (sp.symm (m0, mj)).2).1, ν), (pl (sp.symm (m0, mj)).2).2) = ((pl0 m0, ν), plj mj)
        rw [e]
      · rintro m0 ⟨mj, ν⟩
        have e : pl (sp.symm (m0, mj)).2 = (pl0 m0, plj mj) := h.plain_join m0 mj
        show ((pl (sp.symm (m0, mj)).2).1, ((pl (sp.symm (m0, mj)).2).2, ν)) = (pl0 m0, (plj mj, ν))
        rw [e]
  · show r.rd (Round.stripMsg ((a.grind W b).join m0 mj)).1 p =
      r.rd (Round.stripMsg ((a.grind W b).join m0 mj')).1 p
    rw [strip_join, strip_join]
    exact h.rd_shared _ _ _ p hp
  · show r.rd (Round.stripMsg ((a.grind W b).join m0 mj)).1 p =
      r.rd (Round.stripMsg ((a.grind W b).join m0' mj)).1 p
    rw [strip_join, strip_join]
    exact h.rd_own _ _ _ p hp

theorem coherent_grind :
    ∀ {s : Shape} {A : RoundSplits s} (g : GBits s), A.Coherent → (A.grind W g).Coherent
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (b, g), h => ⟨coherent_round h.1 b, coherent_grind g h.2⟩

theorem fmtFrom_grind :
    ∀ {s : Shape} {A : RoundSplits s} (g : GBits s) (ph : FPhase),
      RoundSplits.FmtFrom s A ph → RoundSplits.FmtFrom (s.grind W g) (A.grind W g) ph
  | [], _, _, _, _ => trivial
  | _ :: _, (a, A), (b, g), ph, h => by
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k
      · cases ph
        · exact h
        · exact fmtFrom_grind (A := A) g .shr h
        · refine ⟨⟨h.1.1, ?_⟩, fmtFrom_grind (A := A) g .shr h.2⟩
          cases b <;> exact h.1.2
        · exact h
      · refine ⟨⟨h.1.1, ?_⟩, fmtFrom_grind (A := A) g ph.afterLo h.2⟩
        cases b <;> exact h.1.2

theorem localTo_grind :
    ∀ {n : ℕ} {s : Shape} {A : RoundSplits s} (g : GBits s),
      RoundSplits.LocalTo n s A → RoundSplits.LocalTo n (s.grind W g) (A.grind W g)
  | _, [], _, _, h => by cases ‹ℕ› <;> exact False.elim h
  | 0, _ :: _, (_, _), (_, _), h => h
  | _ + 1, _ :: _, (_, _), (_, g), h => ⟨h.1, localTo_grind g h.2⟩

/-! ## 3. Prefixes of transcripts; the new state function -/

def stripP : {s : Shape} → (g : GBits s) → AtP (s.grind W g) → AtP s
  | _ :: _, (_, _), .inl _ => .inl ()
  | _ :: _, (_, g), .inr (m, c, τ) => .inr (Round.stripMsg m, GChal.old c, stripP g τ)

def stripV : {s : Shape} → (g : GBits s) → AtV (s.grind W g) → AtV s
  | _ :: _, (_, _), .inl m => .inl (Round.stripMsg m)
  | _ :: _, (_, g), .inr (m, c, τ) => .inr (Round.stripMsg m, GChal.old c, stripV g τ)

/-- A prefix of a transcript, without nonces and proof-of-work bits. -/
def strip {s : Shape} (g : GBits s) : PTr (s.grind W g) → PTr s
  | .atP τ => .atP (stripP g τ)
  | .atV τ => .atV (stripV g τ)
  | .full τ => .full (Tr.strip g τ)

def passP : {s : Shape} → (g : GBits s) → AtP (s.grind W g) → Bool
  | _ :: _, (_, _), .inl _ => true
  | _ :: _, (_, g), .inr (_, c, τ) => GChal.pass c && passP g τ

def passV : {s : Shape} → (g : GBits s) → AtV (s.grind W g) → Bool
  | _ :: _, (_, _), .inl _ => true
  | _ :: _, (_, g), .inr (_, c, τ) => GChal.pass c && passV g τ

/-- All proof-of-work bits in a prefix of a transcript are 0. -/
def pass {s : Shape} (g : GBits s) : PTr (s.grind W g) → Bool
  | .atP τ => passP g τ
  | .atV τ => passV g τ
  | .full τ => Rho.pass g τ.rho

theorem strip_empty : ∀ {s : Shape} (g : GBits s), strip g (PTr.empty (s.grind W g)) = PTr.empty s
  | [], _ => rfl
  | _ :: _, (_, _) => rfl

theorem pass_empty : ∀ {s : Shape} (g : GBits s), pass g (PTr.empty (s.grind W g)) = true
  | [], _ => rfl
  | _ :: _, (_, _) => rfl

theorem strip_cons {r : Round} {s : Shape} (b : ℕ) (g : GBits s)
    (m : (r.grind W b).Msg) (c : (r.grind W b).Chal) :
    ∀ t : PTr (s.grind W g), strip (s := r :: s) (b, g) (PTr.cons m c t) =
      PTr.cons (Round.stripMsg m) (GChal.old c) (strip g t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem pass_cons {r : Round} {s : Shape} (b : ℕ) (g : GBits s)
    (m : (r.grind W b).Msg) (c : (r.grind W b).Chal) :
    ∀ t : PTr (s.grind W g), pass (s := r :: s) (b, g) (PTr.cons m c t) = (GChal.pass c && pass g t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

/-- The new state function: the flag, all tests so far are passed, and the old state of the stripped
transcript is 1. -/
def gst {s : Shape} (g : GBits s) (fl : Bool) (S : PTr s → Bool) : PTr (s.grind W g) → Bool :=
  fun t => fl && (pass g t && S (strip g t))

theorem gst_empty {s : Shape} (g : GBits s) (fl : Bool) (S : PTr s → Bool) :
    gst g fl S (PTr.empty (s.grind W g)) = (fl && S (PTr.empty s)) := by
  unfold gst
  rw [pass_empty, strip_empty, Bool.true_and]

theorem gst_cons {r : Round} {s : Shape} (b : ℕ) (g : GBits s) (fl : Bool) (S : PTr (r :: s) → Bool)
    (m : (r.grind W b).Msg) (c : (r.grind W b).Chal) (t : PTr (s.grind W g)) :
    gst (s := r :: s) (b, g) fl S (PTr.cons m c t) =
      gst g (fl && GChal.pass c) (fun u => S (PTr.cons (Round.stripMsg m) (GChal.old c) u)) t := by
  unfold gst
  rw [pass_cons, strip_cons, Bool.and_assoc, Bool.and_assoc]

theorem gst_false {s : Shape} (g : GBits s) (S : PTr s → Bool) (t : PTr (s.grind W g)) :
    gst g false S t = false := rfl

open BatchH4 in
theorem proverLaw_grind :
    ∀ {s : Shape} (g : GBits s) (fl : Bool) (S : PTr s → Bool),
      ProverLaw s S → ProverLaw (s.grind W g) (gst g fl S)
  | _ :: _, (_, _), fl, S, h, .inl _, m, h0 => by
      cases fl
      · rfl
      · exact h (.inl ()) (Round.stripMsg m) h0
  | r :: s, (b, g), fl, S, h, .inr (m', c', τ), m, h0 => by
      have h0' : gst (s := r :: s) (b, g) fl S (PTr.cons m' c' (.atP τ)) = false := h0
      rw [gst_cons] at h0'
      have h1 := proverLaw_grind g (fl && GChal.pass c')
        (fun u => S (PTr.cons (Round.stripMsg m') (GChal.old c') u)) (h.tail _ _) τ m h0'
      rw [← gst_cons] at h1
      exact h1

theorem idx_stripP : ∀ {s : Shape} (g : GBits s) (τ : AtP (s.grind W g)), (stripP g τ).idx = τ.idx
  | _ :: _, (_, _), .inl _ => rfl
  | _ :: _, (_, g), .inr (_, _, τ) => congrArg (· + 1) (idx_stripP g τ)

/-! ## 4. The soundness property `SndB` (Snd-B) and its late form -/

/-- If the new state after a challenge is 1: the flag is true, the challenge's proof-of-work bits
are 0, the old state of the stripped prefix is 1. -/
theorem gst_step {r : Round} {s : Shape} (b : ℕ) (g : GBits s) (fl : Bool) (S : PTr (r :: s) → Bool)
    (m : (r.grind W b).Msg) (c : (r.grind W b).Chal)
    (h : gst (s := r :: s) (b, g) fl S (PTr.cons m c (PTr.empty (s.grind W g))) = true) :
    fl = true ∧
    GChal.pass c = true ∧
    S (PTr.cons (Round.stripMsg m) (GChal.old c) (PTr.empty s)) = true := by
  rw [gst_cons, gst_empty, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem gst_atV {r : Round} {s : Shape} (b : ℕ) (g : GBits s)
    (S : PTr (r :: s) → Bool) (m : (r.grind W b).Msg) :
    gst (s := r :: s) (b, g) true S (.atV (Sum.inl m)) = S (.atV (Sum.inl (Round.stripMsg m))) :=
  rfl

/-- The condition on the challenge of one round is preserved, with the same count e. Jn' j, Jn j are
the prover messages in the transcripts of slot j, new and old (`sj`: Jn j is the stripped Jn' j). -/
theorem round_grind {N : ℕ} {r : Round} {s : Shape} (b : ℕ) (g : GBits s) (e : ℕ)
    (St : Fin N → Option (PTr (r :: s) → Bool)) (fl : Fin N → Bool)
    (Jn' : Fin N → (r.grind W b).Msg)
    (Jn : Fin N → r.Msg) (sj : ∀ j, Round.stripMsg (Jn' j) = Jn j) : ∀ k : Kind,
    (match k with
      | .lo =>
        ∀ j S, St j = some S → S (.atV (Sum.inl (Jn j))) = false →
          cnt (fun c : r.Chal => S (PTr.cons (Jn j) c (PTr.empty s)) = true) ≤ e
      | .sh =>
        cnt (fun c : r.Chal =>
            ∃ j S,
              St j = some S ∧
              S (.atV (Sum.inl (Jn j))) = false ∧
              S (PTr.cons (Jn j) c (PTr.empty s)) = true) ≤ e) →
    (match k with
      | .lo =>
        ∀ j S, (St j).map (gst (s := r :: s) (b, g) (fl j)) = some S →
          S (.atV (Sum.inl (Jn' j))) = false →
          cnt (fun c : (r.grind W b).Chal =>
              S (PTr.cons (Jn' j) c (PTr.empty (Shape.grind W s g))) = true) ≤ e
      | .sh => cnt (fun c : (r.grind W b).Chal =>
          ∃ j S,
            (St j).map (gst (s := r :: s) (b, g) (fl j)) = some S ∧
            S (.atV (Sum.inl (Jn' j))) = false ∧
          S (PTr.cons (Jn' j) c (PTr.empty (Shape.grind W s g))) = true) ≤ e)
  | .sh => fun hround => by
      -- a shared round: the joint event; one vector of proof-of-work bits for all slots
      refine le_trans
        (cnt_mono (Q := fun c : GChal b r.Chal =>
              GChal.pass c = true ∧
              ∃ j S,
                St j = some S ∧
                S (.atV (Sum.inl (Jn j))) = false ∧
                S (PTr.cons (Jn j) (GChal.old c) (PTr.empty s)) = true) ?_)
        ((GChal.cnt_pass b _).le.trans hround)
      rintro c ⟨j, S', hS', h0, h1⟩
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      obtain ⟨hf, hp, h1'⟩ := gst_step b g (fl j) S _ c h1
      rw [hf, gst_atV] at h0
      rw [sj] at h0 h1'
      exact ⟨hp, j, S, hS, h0, h1'⟩
  | .lo => fun hround j S' hS' h0 => by
      -- a local round: each slot by itself
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      cases hf : fl j
      · exact (le_of_eq (cnt_false fun c hc => Bool.false_ne_true hc)).trans (Nat.zero_le e)
      · rw [hf, gst_atV, sj] at h0
        refine le_trans
          (cnt_mono (Q := fun c : GChal b r.Chal =>
                GChal.pass c = true ∧ S (PTr.cons (Jn j) (GChal.old c) (PTr.empty s)) = true)
            fun c hc => ?_)
          ((GChal.cnt_pass b _).le.trans (hround j S hS h0))
        obtain ⟨_, hp, h1'⟩ := gst_step b g true S _ c hc
        rw [sj] at h1'
        exact ⟨hp, h1'⟩

theorem jointLaw_grind {N : ℕ} :
    ∀ {s : Shape} (g : GBits s) (A : RoundSplits s) (ε : Err s)
        (St : Fin N → Option (PTr s → Bool)) (fl : Fin N → Bool),
      JointLaw N s A ε St →
      JointLaw N (s.grind W g) (A.grind W g) (Err.grind g ε) (fun j => (St j).map (gst g (fl j)))
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (b, g), (a, A), (e, ε), St, fl, h => by
      intro (m0 : (a.grind W b).M0) (m : Fin N → (a.grind W b).Mj)
      obtain ⟨hround, hrest⟩ := h (GPlain.old m0) (fun j => GPlain.old (m j))
      refine ⟨round_grind b g e St fl (fun j => (a.grind W b).join m0 (m j))
          (fun j => a.join (GPlain.old m0) (GPlain.old (m j)))
          (fun j => strip_join a b m0 (m j)) a.kind hround,
        fun v => ?_⟩
      have ih := jointLaw_grind g A ε _ (fun j => fl j && GChal.pass (a.kind.slot v j))
        (hrest (a.kind.mapAll GChal.old v))
      refine cast (congrArg (JointLaw N (Shape.grind W s g) (A.grind W g) (Err.grind g ε)) ?_) ih
      funext j
      beta_reduce
      refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
      congr 1
      funext S t
      show gst g (fl j && GChal.pass (a.kind.slot v j))
          (fun u =>
            S (PTr.cons (a.join (GPlain.old m0) (GPlain.old (m j)))
                (a.kind.slot (a.kind.mapAll GChal.old v) j) u)) t =
        gst (s := r :: s) (b, g) (fl j) S
          (PTr.cons ((a.grind W b).join m0 (m j)) (a.kind.slot v j) t)
      rw [gst_cons, slot_mapAll, strip_join]
      rfl

variable {X : Type} {E : ExtSpec}

theorem full_grind {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape) (S : PTr Q.loc.shape → Bool) (x : X)
    (y : E.Str) (h3 : ∀ τ : Tr Q.loc.shape, S (.full τ) = false → Q.loc.accept x y τ = false)
    (τ : Tr (Q.loc.shape.grind W g)) (hτ : gst g true S (.full τ) = false) :
    (Q.grind W g).loc.accept x y τ = false := by
  show (Rho.pass g τ.rho && Q.loc.accept x y (Tr.strip g τ)) = false
  have hτ' : (Rho.pass g τ.rho && S (.full (Tr.strip g τ))) = false := hτ
  cases hp : Rho.pass g τ.rho
  · rfl
  · rw [hp, Bool.true_and] at hτ'
    rw [Bool.true_and]
    exact h3 _ hτ'

theorem sndB_grind {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape) {N : ℕ} {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (h : Q.SndB N L ε) :
    (Q.grind W g).SndB N L (Err.grind g ε) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  refine ⟨fun y x => gst g true (State y x),
    fun y x => ?_,
    fun y x => proverLaw_grind g true (State y x) (h2 y x),
    fun y x τ hτ => full_grind g (State y x) x y (h3 y x) τ hτ,
    fun y x => ?_⟩
  · show gst g true (State y x) (PTr.empty (Q.loc.shape.grind W g)) = true ↔ _
    rw [gst_empty, Bool.true_and]
    exact h1 y x
  · refine cast (congrArg (JointLaw N (Q.loc.shape.grind W g) (Q.ann.grind W g) (Err.grind g ε)) ?_)
      (jointLaw_grind g Q.ann ε _ (fun _ => true) (h4 y x))
    funext j
    cases x j <;> rfl

theorem sndBL_grind {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape) {N : ℕ} {early : X → X}
    {late : Option ℕ} {L : X → E.Str → Prop} {ε : Err Q.loc.shape} (h : Q.SndBL N early late L ε) :
    (Q.grind W g).SndBL N early late L (Err.grind g ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  refine ⟨fun n hn => ⟨(h0 n hn).1, localTo_grind g (h0 n hn).2⟩,
    fun y x => gst g true (State y x),
    fun y x hL => ?_,
    fun y x => proverLaw_grind g true (State y x) (h2 y x),
    fun y x τ hL hn hτ => ?_,
    fun y x τ hL hτ => full_grind g (State y _) x y (fun τ' => h3 y x τ' hL) τ hτ,
    fun y x => ?_⟩
  · show gst g true (State y (early x)) (PTr.empty (Q.loc.shape.grind W g)) = false
    rw [gst_empty, Bool.true_and]
    exact h1 y x hL
  · show (true && (passP g τ && State y x (.atP (stripP g τ)))) = false
    have hτ' : (true && (passP g τ && State y (early x) (.atP (stripP g τ)))) = false := hτ
    cases hp : passP g τ
    · rfl
    · rw [hp, Bool.true_and, Bool.true_and] at hτ'
      rw [Bool.true_and, Bool.true_and]
      exact hsw y x (stripP g τ) hL (by rw [idx_stripP]; exact hn) hτ'
  · refine cast (congrArg (JointLaw N (Q.loc.shape.grind W g) (Q.ann.grind W g) (Err.grind g ε)) ?_)
      (jointLaw_grind g Q.ann ε _ (fun _ => true) (h4 y x))
    funext j
    cases x j <;> rfl

/-! ## 5. Positions read in the external string -/

theorem allReads_grind (Q : BatchInteractiveOracleProof X E) (g : GBits Q.loc.shape) {N : ℕ} (x : Fin N → Option X)
    (ρ : BRho N (Q.loc.shape.grind W g) (Q.ann.grind W g)) :
    (Q.grind W g).allReads x ρ = Q.allReads x (BRho.strip g ρ) := by
  classical
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.biUnion_congr rfl fun j _ => ?_
  cases x j with
  | none => rfl
  | some xj =>
    show Q.loc.extReads xj (Rho.strip g (ρ.slot j)) = Q.loc.extReads xj ((BRho.strip g ρ).slot j)
    rw [slot_strip]

theorem readsAtMost_grind {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape)
    {N q : ℕ} (h : Q.ReadsAtMost N q) : (Q.grind W g).ReadsAtMost N q :=
  fun x ρ => by rw [allReads_grind]; exact h x _

theorem extShared_grind {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape) (h : Q.ExtShared) :
    (Q.grind W g).ExtShared :=
  fun x x' ρ ρ' hρ =>
    h x x' (Rho.strip g ρ) (Rho.strip g ρ')
      (by rw [← sh_strip, ← sh_strip]; exact congrArg (RhoSh.strip g) hρ)

/-! ## 6. One slot of the honest prover -/

theorem zip_grind :
    ∀ {s : Shape} (g : GBits s) {A : RoundSplits s} (a : SStrat s A) (b : LStrat s A) (ν : GNon W s),
      (SStrat.grind g a ν).zip (LStrat.grind g b ν) = Strat.grind g (a.zip b) (NStrat.const g ν)
  | [], _, _, _, _, _ => rfl
  | r :: s, (b, g), (an, A), (m0, k0), (mj, kj), (ν, νs) => by
      show ((an.grind W b).join (GPlain.mk (an.kind.b0 b) m0 ν) (GPlain.mk (an.kind.bJ b) mj ν),
          fun c : GChal b r.Chal =>
            (SStrat.grind g (k0 (an.kind.mapSh GChal.old (an.kind.shOf c))) νs).zip
              (LStrat.grind g (kj (GChal.old c)) νs)) =
        ((Round.fillMsg b (an.join m0 mj) ν,
          fun c : GChal b r.Chal =>
            Strat.grind g ((k0 (an.kind.shOf (GChal.old c))).zip (kj (GChal.old c)))
              (NStrat.const g νs)) : (r.grind W b).Msg ×
            (GChal b r.Chal → Strat (Shape.grind W s g) Unit))
      rw [join_mk]
      congr 1
      funext c
      rw [shOf_map, zip_grind]

variable {Wt : Type}

theorem one_strat_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) (w : Wt) (x : X) (c : H.Coin0 × H.Coin) :
    (H.grind g ν).one.strat w x c = Strat.grind g (H.one.strat w x c) (NStrat.const g ν) :=
  zip_grind g _ _ ν

theorem mem_one_withheld_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) (w : Wt) (x : X) (ρ : Rho (Q.loc.shape.grind W g)) :
    ρ ∈ (H.grind g ν).one.withheld w x ↔ Rho.strip g ρ ∈ H.one.withheld w x := by
  show ((RhoLo.strip g (Rho.lo (Q.ann.grind W g) ρ) ∈ H.Bad ∨
        H.stop0 (RhoSh.strip g (Rho.sh (Q.ann.grind W g) ρ)) = true) ∨
      RhoLo.strip g (Rho.lo (Q.ann.grind W g) ρ) ∈ H.Hid w x) ↔
    ((Rho.lo Q.ann (Rho.strip g ρ) ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann (Rho.strip g ρ)) = true) ∨
      Rho.lo Q.ann (Rho.strip g ρ) ∈ H.Hid w x)
  rw [lo_strip, sh_strip]

theorem accept_one_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) (w : Wt) (x : X) (c : H.Coin0 × H.Coin)
    (ρ : Rho (Q.loc.shape.grind W g)) (y : E.Str) :
    (Q.grind W g).loc.accept x y (((H.grind g ν).one.strat w x c).run ρ).1 =
      (Rho.pass g ρ && Q.loc.accept x y ((H.one.strat w x c).run (Rho.strip g ρ)).1) := by
  rw [one_strat_grind]
  exact Q.loc.accept_run_grind g _ _ ρ x y

theorem prRho_one_withheld_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) (w : Wt) (x : X) :
    prRho ((H.grind g ν).one.withheld w x) = prRho (H.one.withheld w x) := by
  have e : (H.grind g ν).one.withheld w x = {ρ | Rho.strip g ρ ∈ H.one.withheld w x} :=
    Set.ext fun ρ => mem_one_withheld_grind H g ν w x ρ
  rw [e]
  exact prRho_strip g _

/-! ## 7. The uniform distribution -/

theorem map_mapAll_unif {N : ℕ} (b : ℕ) (C : Type) [Fintype C] [Nonempty C] :
    ∀ k : Kind, (unif (k.All N (GChal b C))).map (k.mapAll GChal.old) = unif (k.All N C)
  | .sh => GChal.map_old_unif b C
  | .lo =>
    map_unif_pi (Ω := fun _ : Fin N => GChal b C) (Y := fun _ : Fin N => C)
      (fun _ => GChal.old) fun _ => GChal.map_old_unif b C

theorem map_strip_unif {N : ℕ} :
    ∀ (s : Shape) (g : GBits s) (A : RoundSplits s),
      (unif (BRho N (s.grind W g) (A.grind W g))).map (BRho.strip g) = unif (BRho N s A)
  | [], _, _ => PMF.map_id _
  | r :: s, (b, g), (a, A) =>
    map_unif_prodMap (Ω₁ := a.kind.All N (GChal b r.Chal))
      (Ω₂ := BRho N (Shape.grind W s g) (A.grind W g)) (Y₁ := a.kind.All N r.Chal)
      (Y₂ := BRho N s A) (a.kind.mapAll GChal.old) (BRho.strip g)
      (map_mapAll_unif b r.Chal a.kind) (map_strip_unif s g A)

theorem prBRho_strip {N : ℕ} {s : Shape} (g : GBits s) {A : RoundSplits s} (S : Set (BRho N s A)) :
    prBRho {ρ : BRho N (s.grind W g) (A.grind W g) | BRho.strip g ρ ∈ S} = prBRho S := by
  unfold prBRho
  rw [← map_strip_unif (W := W) s g A, pr_map]
  rfl

/-! ## 8. Outputs, the simulator, honest-verifier zero knowledge for sets of slots -/

theorem slotOut_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) (w : Wt) (ox : Option X)
    (ρ : Rho (Q.loc.shape.grind W g)) (c : H.Coin0 × H.Coin) :
    slotOut (H.grind g ν) w ox ρ c = (slotOut H w ox (Rho.strip g ρ) c).map (DView.fill g ν) := by
  classical
  cases ox with
  | none => rfl
  | some xj =>
    by_cases h : Rho.strip g ρ ∈ H.one.withheld w xj
    · have e1 : slotOut (H.grind g ν) w (some xj) ρ c = none :=
        if_pos ((mem_one_withheld_grind H g ν w xj ρ).2 h)
      have e2 : slotOut H w (some xj) (Rho.strip g ρ) c = none := if_pos h
      rw [e1, e2]
      rfl
    · have e1 : slotOut (H.grind g ν) w (some xj) ρ c =
          some ((Q.loc.grind W g).dview xj (H.ext w) (((H.grind g ν).one.strat w xj c).run ρ).1) :=
        if_neg fun hm => h ((mem_one_withheld_grind H g ν w xj ρ).1 hm)
      have e2 : slotOut H w (some xj) (Rho.strip g ρ) c =
          some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj c).run (Rho.strip g ρ)).1) := if_neg h
      rw [e1, e2, one_strat_grind]
      exact congrArg some (InteractiveOracleProof.dview_run_grind g ν (H.one.strat w xj c) xj (H.ext w) ρ)

theorem output_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N (Q.loc.shape.grind W g) (Q.ann.grind W g)) (J : Finset (Fin N)) :
    (H.grind g ν).output w x ρ J =
      (H.output w x (BRho.strip g ρ) J).map (DView.fillJ g (fun _ => ν)) := by
  rw [output_eq, output_eq, PMF.map_comp]
  refine congrArg (fun f => PMF.map f (unif (H.Coin0 × (Fin N → H.Coin)))) ?_
  funext c j
  show slotOut (H.grind g ν) w (x j) (ρ.slot j.1) (c.1, c.2 j) =
    (slotOut H w (x j) ((BRho.strip g ρ).slot j.1) (c.1, c.2 j)).map (DView.fill g ν)
  rw [slotOut_grind, slot_strip]
  rfl

theorem extAnsJ_grind (Q : BatchInteractiveOracleProof X E) (g : GBits Q.loc.shape) {N : ℕ}
    (ρ : BRho N (Q.loc.shape.grind W g) (Q.ann.grind W g)) (J : Finset (Fin N))
    (xs : J → X) (y : E.Str) :
    (Q.grind W g).extAnsJ J xs (fun j => ρ.slot j.1) y =
      Q.extAnsJ J xs (fun j => (BRho.strip g ρ).slot j.1) y := by
  have e : (fun j : J => (BRho.strip g ρ).slot j.1) = fun j : J => Rho.strip g (ρ.slot j.1) :=
    funext fun j => slot_strip j.1 g ρ
  rw [e]
  rfl

theorem sim_grind {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape)
    (ν : GNon W Q.loc.shape) {N : ℕ}
    (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)))
    (w : Wt) (x : Fin N → Option X) (ρ : BRho N (Q.loc.shape.grind W g) (Q.ann.grind W g))
    (J : Finset (Fin N)) (xs : J → X)
    (h : H.output w x (BRho.strip g ρ) J =
      Sim J xs (fun j => (BRho.strip g ρ).slot j.1)
        (Q.extAnsJ J xs (fun j => (BRho.strip g ρ).slot j.1) (H.ext w))) :
    (H.grind g ν).output w x ρ J =
      simGrindB g (fun _ _ => ν) Sim J xs (fun j => ρ.slot j.1)
        ((Q.grind W g).extAnsJ J xs (fun j => ρ.slot j.1) ((H.grind g ν).ext w)) := by
  rw [output_grind, h, extAnsJ_grind]
  have e : (fun j : J => (BRho.strip g ρ).slot j.1) = fun j : J => Rho.strip g (ρ.slot j.1) :=
    funext fun j => slot_strip j.1 g ρ
  rw [e]
  rfl

theorem hvzk_grind {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop}
    {z : ℝ≥0∞} (h : H.HVZK N valid z) (g : GBits Q.loc.shape) (ν : GNon W Q.loc.shape) :
    (H.grind g ν).HVZK N valid z := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨simGrindB g (fun _ _ => ν) Sim, fun w x hv J xs hxs => ?_⟩
  refine le_trans (le_trans (pr_mono _ ?_) (le_of_eq (prBRho_strip g _))) (hS w x hv J xs hxs)
  intro ρ hρ heq
  exact hρ (sim_grind H g ν Sim w x ρ J xs heq)

end BatchGrind

/-! ## 9. The statements -/

open BatchGrind


/-- `BatchProtocol.SoundAt` is preserved, with the lists `Err.grind` (the same counts). -/
theorem BatchProtocol.SoundAt.grind {W : Type} [Inhabited W] {I X : Type} {L : BatchProtocol I X}
    {Rno : I → X → Prop} {εT : Err L.offline.shape} {εL : Err L.link.shape}
    {εB : Err L.onlineBatch.loc.shape} (h : L.SoundAt Rno εT εL εB) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    (L.grind W gT gL gB).SoundAt Rno (Err.grind gT εT) (Err.grind gL εL) (Err.grind gB εB) :=
  ⟨h.sndT.grind gT, h.sndL.grind gL, sndBL_grind gB h.sndB⟩

theorem grindSoundB : Spec.grindSoundB := fun _ _ _ _ _ _ gT gL gB εT εL εB εs' h bT bL bB =>
  (h.grind gT gL gB).sound ((Err.below_grind_iff gT εT εs').2 bT)
    ((Err.below_grind_iff gL εL εs').2 bL) ((Err.below_grind_iff gB εB εs').2 bB)



theorem grindSimB : Spec.grindSimB := fun _ _ _ _ _ _ H g ν _ Sim w x ρ J xs h =>
  sim_grind H g ν Sim w x ρ J xs h

theorem grindUnifB : Spec.grindUnifB := fun _ _ _ _ _ g S => prBRho_strip g S

theorem grindPropsB : Spec.grindPropsB := by
  intro W _ I X L Ryes Rno M gT gL gB εs' h hS
  exact
    { sub := h.sub
      wired := ⟨h.wired.dec_enc, h.wired.extT, h.wired.extL, h.wired.extB⟩
      sound := hS
      reads :=
        ⟨fun x ρ => h.reads.cntT x (Rho.strip gT ρ),
          fun x ρ => h.reads.cntLp x (Rho.strip gL ρ),
          fun x ρ => h.reads.cntLc x (Rho.strip gL ρ),
          readsAtMost_grind gB h.reads.cntB,
          h.reads.hidE⟩
      hidden := ⟨h.hidden.hidT.grind gT _, h.hidden.hidL.grind gL _, hvzk_grind h.hidden.hidB gB _⟩
      prT := fun w x => (le_of_eq (L.honestOfflineProver.prRho_withheld_grind gT _ w x)).trans (h.complete.prT w x)
      prL := fun w x => (le_of_eq (L.honestLinkProver.prRho_withheld_grind gL _ w x)).trans (h.complete.prL w x)
      prB := fun w x hv =>
        (le_of_eq (prRho_one_withheld_grind L.honestOnlineBatchProver gB _ w x)).trans (h.complete.prB w x hv)
      localT := h.localT.grind gT
      localL := h.localL.grind gL
      localB := h.localB.grind gB
      cohB := coherent_grind gB h.cohB
      pointT := h.pointT.map fun p => p.grind gT
      pointL := h.pointL.map fun p => p.grind gL
      pointB := h.pointB.map fun p => p.grind gB }

end Iop
