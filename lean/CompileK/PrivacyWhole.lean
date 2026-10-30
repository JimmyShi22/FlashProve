-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/PrivacyWhole.lean: the compiler takes honest-verifier zero knowledge of the whole object:
index privacy of the compiled argument with `HVZKWhole` (Hiop/Whole.lean) as its zero-knowledge
hypothesis on the protocol, and `GrFitPB W` (Compile/Batch/SpecFit.lean), the interface's privacy
part, beside it (its other hypotheses: after Part 7).

Definitions, statements and proofs.
It was asked that the argument be built in two steps: first an information-theoretic object that is
honest-verifier zero-knowledge in the sense of ONE definition, then a standard compiler
(lean/CREDITS.md).
The compiler's privacy theorem (`privacyKEGrWithBOf`, Compile/Batch/PubProgMainBGr.lean) is stated
from run-by-run facts: good simulators of single runs (`Sims.Good`), the counts of positions read
and "an encoded index hides b positions" (`BatchProtocol.Reads`), the budget. Its proof uses these facts in
one place, the lifetime theorem for the star of encodings (`Spec.lifeStarBWith`,
Compile/Batch/SpecLifeStar.lean), applied to an adversary that is made from the adversarial
verifier. Here that one use is replaced.

Main names, by the parts of the file:
  Part 1, `envPre`, `envPost`, `envLinks`: from an adversary against the game of the star (coins,
    oracle queries, "setup", batches on leaves) an environment of Hiop/Whole.lean: its coins, the
    lazily sampled oracle answers and the placement of a batch are coins of the environment
    (`Env.draw`); "setup" asks for m further encoded indices (`Env.fresh`); a batch on leaf j is a
    session on the encoded index j + 1 in which the adversary's own slots are shown and the other
    slots are empty (`Env.session`). It never reads a single position (no `Env.read`).
  Part 2, `starHost`: one host for arbitrary laws of the three kinds of runs; the real host and the
    simulator's host are two instances, by definition (`realHost_eq`, `simHost_eq`).
  Part 3, `run_pre`: the game of the star (`StarWB`, `LifeB`, Compile/Batch/SpecLifeStar.lean) is
    the experiment of the whole object with that environment: an equality of laws, for admissible
    adversaries. (In the experiment the offline phase comes first; in the game the adversary may
    toss coins and ask oracles before "setup". The two orders give the same law.)
  Part 4, `starBounds`, `adm_pre`: an admissible adversary gives an environment within the bounds:
    nenc = m, no session on number 0, at most s1 on each further encoded index, no single reads,
    shown = maxBatchSize.
  Part 5, `lifeStar_of_whole`: so HVZKWhole at these bounds, with the simulator simWhole L Sm i₀
    and the error z, gives the conclusion of the lifetime theorem with the bound z.
  Part 6, `privacyWhole : Spec.privacyWhole`: Gen.HasIndexPrivacyWith (relPair Ryes Rno _) (argBKE
    W WP p) B (simBKGr W p Sm i₀) (zetaWhole p hb z), zetaWhole p hb z t n = leaves · binTail n
    leaves s1 + hb t n + z, for every hb that bounds one passage to fresh answers
    (`HopU W p B hb`). `privacyWholeTot`: at hb = hashTermsBGTot W p.
  Part 7, `starBounds_fits`, `starBounds_err`, `privacy_of_runs`: under the hypotheses of
    `privacy_of_runs`, a check that the hypothesis can be met: the run-by-run facts give it
    (`hvzk_whole`, Hiop/WholeProof.lean), with z = zT + leaves · zL + leaves · s1 · (maxBatchSize · zO).
Hypotheses of `privacyWhole` beside HVZKWhole and `HopU W p B hb` (told under Part 6), of which
`GrFitPB W` is by its own docstring "the privacy part, for the three protocols of an interface"
(Compile/Batch/SpecFit.lean), and `WP.OK` asks that the enumerations of the encoding randomness, of
the placements and of the honest sides' coins are bijective (`WireBP.OK`, Iop/BatchWireP.lean),
which is what makes each of these draws uniform; none of the others is about hiding: R_yes ⊆ R_no;
`L.Wired` (the honest sides speak of the encodings); the annotation of Batch is coherent and has a
format; the laws of the wires (`W.OKG`, which has the clause `chal_unif` (`WireRB.OKG`,
Iop/BatchWire.lean), `GrFitPB W`, `WP.OK`); B ≤ maxBatchSize.

Limits: the simulator in the hypothesis is the named one, simWhole L Sm i₀, for some triple Sm of
functions of the types of run simulators, of which nothing is asked: the compiled simulator simBKGr
W p Sm i₀ is built from the same Sm. It is not a theorem for an arbitrary `Hiop.Simulator`. The
error z does not grow with the number n of batches: it is the error at the bounds, which allow
leaves · s1 sessions. The interface L is the one that is compiled: for the data `DataK` that is the
interface after verifier messages are made from blocks (`L.draws dr`), so HVZKWhole is needed of
that interface. What Hiop/Whole.lean's header lists as differences from the definition of the work
that this protocol builds on (lean/CREDITS.md, "Further work") stays.

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeProof
import Compile.Batch.PubProgMainBGr
import Compile.Batch.HopTot

set_option autoImplicit false

noncomputable section

namespace Hiop.Star
open Prob Iop Rom Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : BatchProtocol I X} {S : OSpec} {α : Type}

/-! ## Part 1. From an adversary against the game of the star to an environment -/

/-- After "setup". Coins, the lazy answers of the oracles and the placement of a batch are coins of
the environment; a batch on leaf j is a session on the encoded index number j + 1, with the
adversary's own slots shown and the other slots empty. T: the table of the oracle answers given so
far. (A second "setup" is answered like a batch on a leaf that does not exist; no admissible
adversary makes one.) -/
def envPost (m : ℕ) : Adv S (LifeOutB X) (LifeInB L) α → Table S → Env L α
  | .halt a, _ => .stop a
  | .sample n k, T => .draw (Fin (n + 1)) (PMF.uniformOfFintype (Fin (n + 1))) fun r => envPost m (k r) T
  | .query o q k, T => .draw (S.Rng o × Table S) (lazyAnswer T o q) fun y => envPost m (k y.1) y.2
  | .call (.inl ()) k, T => envPost m (k (.inr none)) T
  | .call (.inr (j, xs)) k, T =>
      if j < m then
        .draw (Equiv.Perm (Fin L.maxBatchSize)) (unif (Equiv.Perm (Fin L.maxBatchSize))) fun σ =>
          .session (j + 1) (slotsOf σ xs.length) (ownAt σ xs) (fun _ => none) fun a =>
            envPost m (k (.inr (some (slotList σ xs.length, ⟨slotsOf σ xs.length, a⟩)))) T
      else envPost m (k (.inr none)) T

/-- n further encoded indices; then K, with what was shown of their links, in their order -/
def envLinks : ℕ → (List (Sess L.link) → Env L α) → Env L α
  | 0, K => K []
  | n + 1, K => .fresh fun s => envLinks n fun t => K (s :: t)

/-- Before "setup". a: what was shown of the offline IOP; the environment has it from the start and
hands it to the adversary when that calls "setup". -/
def envPre (m : ℕ) : Adv S (LifeOutB X) (LifeInB L) α → Table S → Sess L.offline → Env L α
  | .halt a, _, _ => .stop a
  | .sample n k, T, a => .draw (Fin (n + 1)) (PMF.uniformOfFintype (Fin (n + 1))) fun r => envPre m (k r) T a
  | .query o q k, T, a => .draw (S.Rng o × Table S) (lazyAnswer T o q) fun y => envPre m (k y.1) y.2 a
  | .call (.inl ()) k, T, a => envLinks m fun ls => envPost m (k (.inl (a, ls))) T
  | .call (.inr _) k, T, a => envPre m (k (.inr none)) T a

/-! ## Part 2. One host for arbitrary laws of the three kinds of runs -/

section Host
variable (sT : L.EncodingRandomness → PMF (Sess L.offline)) (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (sB : L.EncodingRandomness → BLaw L)
  (rd : ℕ × (ℕ → L.EncodingRandomness) → ℕ → Fin L.wordLength → PMF (L.Symbol × (ℕ × (ℕ → L.EncodingRandomness))))

/-- the host whose runs have the laws sT, sL, sB, as functions of the encoding randomness -/
def starHost : Host L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r => (sT r).map fun a => (a, (0, fun _ => r))
  fresh := fun s =>
    (unif L.EncodingRandomness).bind fun r =>
      (sL (s.2 0) r).map fun a => (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs rest => (sB (s.2 e) J xs rest).map fun a => (a, s)
  read := rd

end Host

theorem realHost_eq (L : BatchProtocol I X) (i : I) :
    realHost L i =
      starHost (fun r => sess L.honestOfflineProver (i, r) ()) (fun r r' => sess L.honestLinkProver (i, r, r') ())
        (fun r J xs rest => bsess L.honestOnlineBatchProver (i, r) (vec J xs rest) J)
        (fun s e p => PMF.pure (L.encodeIndex i (s.2 e) p, s)) := rfl

theorem simHost_eq (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) :
    (simWhole L Sm i₀).host =
      starHost (fun r => simSess L.offline Sm.T () (L.encodeIndex i₀ r))
        (fun r r' => simSess L.link Sm.Lk () (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
        (fun r J xs _ => simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ r))
        (fun s e p => PMF.pure (L.encodeIndex i₀ (s.2 e) p, s)) := rfl

/-!
## Part 3. The game of the star is the experiment with that environment, for admissible adversaries
-/

/-- the encoding randomness after further encoded indices with the randomness l, when c exist -/
def updMany (ρ : ℕ → L.EncodingRandomness) : ℕ → List L.EncodingRandomness → ℕ → L.EncodingRandomness
  | _, [] => ρ
  | c, r :: t => updMany (Function.update ρ (c + 1) r) (c + 1) t

theorem updMany_le (ρ : ℕ → L.EncodingRandomness) : ∀ (l : List L.EncodingRandomness) (c e : ℕ), e ≤ c → updMany ρ c l e = ρ e := by
  intro l
  induction l generalizing ρ with
  | nil => intro c e _; rfl
  | cons r t ih =>
    intro c e h
    show updMany (Function.update ρ (c + 1) r) (c + 1) t e = ρ e
    rw [ih _ (c + 1) e (by omega), Function.update_of_ne (by omega)]

theorem updMany_get (ρ : ℕ → L.EncodingRandomness) :
    ∀ (l : List L.EncodingRandomness) (c j : ℕ) (h : j < l.length), updMany ρ c l (c + 1 + j) = l[j] := by
  intro l
  induction l generalizing ρ with
  | nil => intro c j h; exact absurd h (by simp)
  | cons r t ih =>
    intro c j h
    show updMany (Function.update ρ (c + 1) r) (c + 1) t (c + 1 + j) = (r :: t)[j]
    cases j with
    | zero => rw [updMany_le _ t (c + 1) (c + 1 + 0) (by omega)]; simp
    | succ j =>
      have := ih (Function.update ρ (c + 1) r) (c + 1) j (by simpa using h)
      rw [show c + 1 + (j + 1) = c + 1 + 1 + j by omega, this]
      simp

section Run
variable (sT : L.EncodingRandomness → PMF (Sess L.offline)) (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (sB : L.EncodingRandomness → BLaw L)
  (rd : ℕ × (ℕ → L.EncodingRandomness) → ℕ → Fin L.wordLength → PMF (L.Symbol × (ℕ × (ℕ → L.EncodingRandomness))))

theorem length_of_linksGB (r₀ : L.EncodingRandomness) : ∀ (n : ℕ), ∀ ls ∈ (linksGB sL r₀ n).support, ls.length = n
  | 0, ls, h => by
      rw [show linksGB sL r₀ 0 = PMF.pure [] from rfl, PMF.support_pure] at h
      rw [Set.mem_singleton_iff.1 h]
      rfl
  | n + 1, ls, h => by
      rw [show linksGB sL r₀ (n + 1) =
          (unif L.EncodingRandomness).bind fun r =>
            (sL r₀ r).bind fun s => (linksGB sL r₀ n).map fun t => (r, s) :: t from rfl] at h
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
      obtain ⟨r, -, s, -, t, ht, rfl⟩ := h
      rw [List.length_cons, length_of_linksGB r₀ n t ht]

theorem run_links :
    ∀ (n : ℕ) (K : List (Sess L.link) → Env L α) (c : ℕ) (ρ : ℕ → L.EncodingRandomness),
      (envLinks n K).run (starHost sT sL sB rd) (c, ρ) =
        (linksGB sL (ρ 0) n).bind fun ls =>
          (K (ls.map Prod.snd)).run (starHost sT sL sB rd) (c + n, updMany ρ c (ls.map Prod.fst))
  | 0, K, c, ρ => by
      rw [show linksGB sL (ρ 0) 0 = PMF.pure [] from rfl, PMF.pure_bind]
      rfl
  | n + 1, K, c, ρ => by
      show ((unif L.EncodingRandomness).bind fun r =>
            (sL (ρ 0) r).map fun a => (a, (c + 1, Function.update ρ (c + 1) r))).bind
          (fun y => (envLinks n fun t => K (y.1 :: t)).run (starHost sT sL sB rd) y.2) = _
      rw [show linksGB sL (ρ 0) (n + 1) =
          (unif L.EncodingRandomness).bind fun r =>
            (sL (ρ 0) r).bind fun s => (linksGB sL (ρ 0) n).map fun t => (r, s) :: t from rfl]
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      refine congrArg _ (funext fun r => congrArg _ (funext fun a => ?_))
      rw [run_links n _ (c + 1) (Function.update ρ (c + 1) r),
        Function.update_of_ne (by omega), show c + 1 + n = c + (n + 1) by omega]
      rfl

theorem reply_some {m : ℕ} {l : List L.EncodingRandomness} {T : Table S} {j : ℕ} {xs : List X}
    {r : L.EncodingRandomness} (h : l[j]? = some r) :
    (StarWB sT sL sB S m).reply (some l, T) (.inr (j, xs)) =
      (placeB L (sB r) xs).map fun o => (.inr (some o), (some l, T)) := by
  show (match (some l : Option (List L.EncodingRandomness)).bind (fun l => l[j]?) with
    | none => PMF.pure ((Sum.inr none : LifeInB L), ((some l, T) : Option (List L.EncodingRandomness) × Table S))
    | some r => (placeB L (sB r) xs).map fun o => ((Sum.inr (some o) : LifeInB L), ((some l, T) : Option (List L.EncodingRandomness) × Table S))) = _
  rw [show (some l : Option (List L.EncodingRandomness)).bind (fun l => l[j]?) = some r from h]

theorem reply_none {m : ℕ} {l : List L.EncodingRandomness} {T : Table S} {j : ℕ} {xs : List X} (h : l[j]? = none) :
    (StarWB sT sL sB S m).reply (some l, T) (.inr (j, xs)) = PMF.pure (.inr none, (some l, T)) := by
  show (match (some l : Option (List L.EncodingRandomness)).bind (fun l => l[j]?) with
    | none => PMF.pure ((Sum.inr none : LifeInB L), ((some l, T) : Option (List L.EncodingRandomness) × Table S))
    | some r => (placeB L (sB r) xs).map fun o => ((Sum.inr (some o) : LifeInB L), ((some l, T) : Option (List L.EncodingRandomness) × Table S))) = _
  rw [show (some l : Option (List L.EncodingRandomness)).bind (fun l => l[j]?) = none from h]

/-- after "setup" -/
theorem run_post {ok : X → Prop} {s1 m : ℕ} (l : List L.EncodingRandomness) (hl : l.length = m) (s : ℕ × (ℕ → L.EncodingRandomness))
    (hs : ∀ (j : ℕ) (h : j < l.length), s.2 (j + 1) = l[j]) :
    ∀ (A : Adv S (LifeOutB X) (LifeInB L) α) (T : Table S) (c : ℕ → ℕ) (n : ℕ),
      LifeAdmB ok s1 A c true n →
      (interact (StarWB sT sL sB S m) A (some l, T)).map Prod.fst =
        (envPost m A T).run (starHost sT sL sB rd) s := by
  intro A
  induction A with
  | halt a => intro T c n _; exact PMF.pure_map _ _
  | sample n' k ih =>
    intro T c n hA
    show ((PMF.uniformOfFintype (Fin (n' + 1))).bind fun r =>
        interact (StarWB sT sL sB S m) (k r) (some l, T)).map Prod.fst =
      (PMF.uniformOfFintype (Fin (n' + 1))).bind fun r =>
        (envPost m (k r) T).run (starHost sT sL sB rd) s
    rw [PMF.map_bind]
    exact congrArg _ (funext fun r => ih r T c n (hA r))
  | query o q k ih =>
    intro T c n hA
    show (((lazyAnswer T o q).map fun a => (a.1, ((some l : Option (List L.EncodingRandomness)), a.2))).bind
        fun y => interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst =
      (lazyAnswer T o q).bind fun y => (envPost m (k y.1) y.2).run (starHost sT sL sB rd) s
    rw [PMF.map_bind, PMF.bind_map]
    exact congrArg _ (funext fun y => ih y.1 y.2 c n (hA y.1))
  | call cl k ih =>
    intro T c n hA
    rcases cl with ⟨⟩ | ⟨j, xs⟩
    · exact absurd hA.1 (by simp)
    · cases n with
      | zero => exact hA.elim
      | succ n =>
        obtain ⟨-, -, -, -, hk⟩ := hA
        show (((StarWB sT sL sB S m).reply (some l, T) (.inr (j, xs))).bind fun y =>
            interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst = _
        by_cases hj : j < m
        · have hjl : j < l.length := by rw [hl]; exact hj
          rw [reply_some sT sL sB (r := s.2 (j + 1))
              (by rw [hs j hjl]; exact List.getElem?_eq_getElem hjl)]
          show _ = (if j < m then _ else _ : Env L α).run (starHost sT sL sB rd) s
          rw [if_pos hj]
          show (((placeB L (sB (s.2 (j + 1))) xs).map fun o =>
                  ((Sum.inr (some o) : LifeInB L), ((some l : Option (List L.EncodingRandomness)), T))).bind
                fun y => interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst =
              (unif (Equiv.Perm (Fin L.maxBatchSize))).bind fun σ =>
                ((sB (s.2 (j + 1)) (slotsOf σ xs.length) (ownAt σ xs) fun _ => none).map
                    fun a => (a, s)).bind fun y =>
            (envPost m (k (.inr (some (slotList σ xs.length, ⟨slotsOf σ xs.length, y.1⟩)))) T).run
              (starHost sT sL sB rd) y.2
          unfold placeB
          simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def]
          exact congrArg _ (funext fun σ => congrArg _ (funext fun a => ih _ T _ n (hk _)))
        · rw [reply_none sT sL sB (List.getElem?_eq_none (by rw [hl]; omega))]
          show ((PMF.pure ((Sum.inr none : LifeInB L), ((some l : Option (List L.EncodingRandomness)), T))).bind
              fun y => interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst =
            (if j < m then _ else _ : Env L α).run (starHost sT sL sB rd) s
          rw [if_neg hj, PMF.pure_bind]
          exact ih _ T _ n (hk _)

/-- Under the hypotheses below, the game of the star is the experiment of the whole object with the
environment made from the adversary. -/
theorem run_pre {ok : X → Prop} {s1 m : ℕ} :
    ∀ (A : Adv S (LifeOutB X) (LifeInB L) α) (T : Table S) (c : ℕ → ℕ) (n : ℕ),
      LifeAdmB ok s1 A c false n →
      (interact (StarWB sT sL sB S m) A (none, T)).map Prod.fst =
        (starHost sT sL sB rd).view fun a => envPre m A T a := by
  intro A
  induction A with
  | halt a =>
    intro T c n _
    exact (PMF.pure_map _ _).trans (PMF.bind_const _ _).symm
  | sample n' k ih =>
    intro T c n hA
    show ((PMF.uniformOfFintype (Fin (n' + 1))).bind fun r =>
        interact (StarWB sT sL sB S m) (k r) (none, T)).map Prod.fst =
      (starHost sT sL sB rd).off.bind fun y =>
        (PMF.uniformOfFintype (Fin (n' + 1))).bind fun r =>
          (envPre m (k r) T y.1).run (starHost sT sL sB rd) y.2
    rw [PMF.map_bind, PMF.bind_comm]
    exact congrArg _ (funext fun r => ih r T c n (hA r))
  | query o q k ih =>
    intro T c n hA
    show (((lazyAnswer T o q).map fun a => (a.1, ((none : Option (List L.EncodingRandomness)), a.2))).bind
        fun y => interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst =
      (starHost sT sL sB rd).off.bind fun y =>
        (lazyAnswer T o q).bind fun u => (envPre m (k u.1) u.2 y.1).run (starHost sT sL sB rd) y.2
    rw [PMF.map_bind, PMF.bind_map, PMF.bind_comm]
    exact congrArg _ (funext fun y => ih y.1 y.2 c n (hA y.1))
  | call cl k ih =>
    intro T c n hA
    rcases cl with ⟨⟩ | ⟨j, xs⟩
    · obtain ⟨-, hk⟩ := hA
      show (((unif L.EncodingRandomness).bind fun r₀ =>
              (sT r₀).bind fun a =>
                (linksGB sL r₀ m).map fun ls =>
                  ((.inl (a, ls.map Prod.snd) : LifeInB L),
                    ((some (ls.map Prod.fst) : Option (List L.EncodingRandomness)), T))).bind
            fun y => interact (StarWB sT sL sB S m) (k y.1) y.2).map Prod.fst =
          ((unif L.EncodingRandomness).bind fun r =>
            (sT r).map fun a => (a, ((0 : ℕ), fun _ : ℕ => r))).bind fun y =>
          (envLinks m fun ls => envPost m (k (.inl (y.1, ls))) T).run (starHost sT sL sB rd) y.2
      simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def]
      refine congrArg _ (funext fun r => congrArg _ (funext fun a => ?_))
      rw [run_links]
      refine Rom.bind_congr_support _ fun ls hls => ?_
      have hlen := length_of_linksGB sL r m ls hls
      refine run_post sT sL sB rd (ls.map Prod.fst) (by rw [List.length_map, hlen]) _
        (fun j h => ?_) _ T c n (hk _)
      have := updMany_get (fun _ : ℕ => r) (ls.map Prod.fst) 0 j h
      rwa [show 0 + 1 + j = j + 1 by omega] at this
    · cases n with
      | zero => exact hA.elim
      | succ n => exact absurd hA.1 (by simp)

end Run

/-! ## Part 4. An admissible adversary gives an environment within the bounds -/

/-- The bounds that the scheme needs: m further encoded indices; no session on number 0 and at most
s1 on each further one; no single reads; any number of the maxBatchSize slots shown. -/
def starBounds (L : BatchProtocol I X) (m s1 : ℕ) : Bounds :=
  ⟨m, fun e => if e = 0 then 0 else s1, fun _ => 0, L.maxBatchSize⟩

theorem adm_post {ok : X → Prop} {s1 m : ℕ} :
    ∀ (A : Adv S (LifeOutB X) (LifeInB L) α) (T : Table S) (c : ℕ → ℕ) (n : ℕ) (us : ℕ → ℕ),
      (∀ j, j < m → us (j + 1) = c j) → LifeAdmB ok s1 A c true n →
      (envPost m A T).Adm (starBounds L m s1) ok m us fun _ => 0 := by
  intro A
  induction A with
  | halt a => intro _ _ _ _ _ _; trivial
  | sample n' k ih => exact fun T c n us hu hA r => ih r T c n us hu (hA r)
  | query o q k ih => exact fun T c n us hu hA y => ih y.1 y.2 c n us hu (hA y.1)
  | call cl k ih =>
    intro T c n us hu hA
    rcases cl with ⟨⟩ | ⟨j, xs⟩
    · exact absurd hA.1 (by simp)
    · cases n with
      | zero => exact hA.elim
      | succ n =>
        obtain ⟨-, hc, -, hok, hk⟩ := hA
        show (if j < m then _ else _ : Env L α).Adm (starBounds L m s1) ok m us fun _ => 0
        by_cases hj : j < m
        · rw [if_pos hj]
          intro σ
          refine ⟨hj, ?_, ?_, fun j' => hok _ (List.getElem_mem _), (fun _ _ h => by cases h),
            fun a => ih _ T _ n _ (fun j' hj' => ?_) (hk _)⟩
          · show us (j + 1) < if j + 1 = 0 then 0 else s1
            rw [if_neg (by omega), hu j hj]
            exact hc
          · exact (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin _))
          · by_cases hjj : j' = j
            · subst hjj
              rw [Function.update_self, Function.update_self, hu j' hj]
            · rw [Function.update_of_ne hjj, Function.update_of_ne (by omega), hu j' hj']
        · rw [if_neg hj]
          exact ih _ T _ n us
            (fun j' hj' => by rw [Function.update_of_ne (by omega), hu j' hj']) (hk _)

theorem adm_links {B : Bounds} {ok : X → Prop} (us ur : ℕ → ℕ) :
    ∀ (n : ℕ) (K : List (Sess L.link) → Env L α) (c : ℕ),
      c + n ≤ B.nenc → (∀ ls, (K ls).Adm B ok (c + n) us ur) → (envLinks n K).Adm B ok c us ur
  | 0, K, c, _, h => h []
  | n + 1, K, c, hc, h => ⟨by omega, fun a => adm_links us ur n _ (c + 1) (by omega) fun ls => by
      have := h (a :: ls)
      rwa [show c + (n + 1) = c + 1 + n by omega] at this⟩

theorem adm_pre {ok : X → Prop} {s1 m : ℕ} :
    ∀ (A : Adv S (LifeOutB X) (LifeInB L) α) (T : Table S) (n : ℕ) (a : Sess L.offline),
      LifeAdmB ok s1 A (fun _ => 0) false n →
      (envPre m A T a).Adm (starBounds L m s1) ok 0 (fun _ => 0) fun _ => 0 := by
  intro A
  induction A with
  | halt a => intro _ _ _ _; trivial
  | sample n' k ih => exact fun T n a hA r => ih r T n a (hA r)
  | query o q k ih => exact fun T n a hA y => ih y.1 y.2 n a (hA y.1)
  | call cl k ih =>
    intro T n a hA
    rcases cl with ⟨⟩ | ⟨j, xs⟩
    · refine adm_links _ _ m _ 0 (by show 0 + m ≤ m; omega) fun ls => ?_
      rw [Nat.zero_add]
      exact adm_post _ T _ n _ (fun _ _ => rfl) (hA.2 _)
    · cases n with
      | zero => exact hA.elim
      | succ n => exact absurd hA.1 (by simp)

/-! ## Part 5. The lifetime statement of the star
From honest-verifier zero knowledge of the whole object. -/

/-- What the compiler's privacy proof uses of the run-by-run facts (the conclusion of
Compile/Batch/SpecLifeStar.lean: Spec.lifeStarBWith, with z for its bound) follows from
honest-verifier zero knowledge of the whole object at the bounds starBounds L m s1, with the same
simulator (in this sense:
`tv ((interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst)`
`((interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst) ≤ z`;
`h : HVZKWhole L Ryes (starBounds L m s1) (simWhole L Sm i₀) z`; `hB`): the game of the star with
its lazily sampled oracles is the experiment of the whole object for an environment made from the
adversary, for admissible adversaries. -/
theorem lifeStar_of_whole (S : OSpec) (L : BatchProtocol I X) (Ryes : I → X → Prop) (m s1 : ℕ) (Sm : Sims L)
    (i₀ : I) (z : ℝ≥0∞) (h : HVZKWhole L Ryes (starBounds L m s1) (simWhole L Sm i₀) z) (i : I)
    (α : Type) (B : Adv S (LifeOutB X) (LifeInB L) α) (n : ℕ)
    (hB : LifeAdmB (Ryes i) s1 B (fun _ => 0) false n) :
    tv ((interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst)
        ((interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst) ≤ z := by
  unfold LifeB simWorldB
  rw [run_pre _ _ _ (fun s e p => PMF.pure (L.encodeIndex i (s.2 e) p, s)) B _ _ n hB,
    run_pre _ _ _ (fun s e p => PMF.pure (L.encodeIndex i₀ (s.2 e) p, s)) B _ _ n hB,
    ← realHost_eq, ← simHost_eq]
  exact h i α _ fun a => adm_pre B _ n a hB

end Hiop.Star

/-! ## Part 6. Index privacy of the compiled argument -/

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB Sims simWorldB)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- ζ: the overrun of a leaf, the hash terms h, the error z of the whole object -/
def zetaWhole (p : Params) (h : ℕ → ℕ → ℝ≥0∞) (z : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun t n => p.leaves * binTail n p.leaves p.s1 + h t n + z

/-- closeness for the token form: closePubUTOf (Compile/Batch/PubProgMainBGr.lean) with its one use
of the lifetime theorem replaced -/
theorem closePubWhole (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x) (hwd : L.Wired)
    (hC : L.onlineBatch.ann.Coherent) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt)
    (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞)
    (hz : Hiop.HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) (Hiop.simWhole L Sm i₀) z)
    (B : ℕ) (hB : B ≤ L.maxBatchSize) {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Close (relPair Ryes Rno hsub) (argBPGT W WP p pw (PpU W WP p) Vf) B
      (asW Unit (WrBP W p pw (simWorldB _ L p.leaves Sm i₀)))
      (iniBP W p pw _ (none, Table.empty _)) (zetaWhole p hb z) := by
  intro i α A t n hA hP
  refine le_trans
    (tv_triangle _
      ((interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
        (iniBP W p pw _ (none, Table.empty _))).map Prod.fst) _)
    (add_le_add
      (realToWrBPUTOf W WP p pw Vf i hwd hC hF hW hG hWP B hB hh _ (fun b hb => hb.1) A t n hA hP)
      ?_)
  have hBeq : ∀ (G : LifeWB W) (s : G.σ),
      (interact (asW Unit (WrBP W p pw G)) A (iniBP W p pw G s)).map Prod.fst =
        (interact G ((wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)).adv
              A (none, LSt.init _)) s).map Prod.fst :=
    fun G s =>
      interact_adv (wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)) G A _ s
  rw [hBeq, hBeq]
  exact Hiop.Star.lifeStar_of_whole _ L Ryes p.leaves p.s1 Sm i₀ z hz i α _ n
    (lifeAdmB_wrapGP W p pw _ _ (Ryes i) A n
      (gAdm_mono (fun b hb => ⟨hb.1.trans hB, hb.2⟩) A false n hP))

theorem privacyPubWhole [Inhabited V] (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x) (hwd : L.Wired)
    (hC : L.onlineBatch.ann.Coherent) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt)
    (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞)
    (hz : Hiop.HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) (Hiop.simWhole L Sm i₀) z)
    (B : ℕ) (hB : B ≤ L.maxBatchSize) {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBPG W WP p pw (PpU W WP p) Vf) B
      (simBPGr W p pw Sm i₀) (zetaWhole p hb z) := by
  refine GlueB.gluePrivacyWith _ _ _ _ Unit _ _ _ _ _ _
    ((WrBP W p pw (simWorldB _ L p.leaves Sm i₀)).pre (ghost W))
    (iniBP W p pw _ (none, Table.empty _)) _
    (Rom.viaConsistent _ _ _ _ _ (ghostPerm I X lam L W) _ (consistent_wrapBP _)) ?_
  rw [argBPG_via W WP p pw (PpU W WP p) Vf hW (routedF_PpU W WP p hW)]
  exact GlueB.closeVia _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ghostPerm I X lam L W)
    (closePubWhole W WP p pw Vf Ryes Rno hsub hwd hC hW hG hWP hF Sm i₀ z hz B hB hh)

/-- The statement of `privacyWhole`: see the head, Part 6 and the hypotheses after Part 7. -/
def Spec.privacyWhole : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x),
    L.Wired → L.onlineBatch.ann.Coherent → L.onlineBatch.ann.Fmt → W.OKG → GrFitPB W → WP.OK →
    ∀ (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞),
      Hiop.HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) (Hiop.simWhole L Sm i₀) z →
      ∀ (B : ℕ), B ≤ L.maxBatchSize →
        ∀ hb : ℕ → ℕ → ℝ≥0∞, HopU W p B hb →
          Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBKE W WP p) B
            (simBKGr W p Sm i₀) (zetaWhole p hb z)

/-- Index privacy of the compiled argument from honest-verifier zero knowledge of the whole object.
(not all hypotheses are named here: see `Spec.privacyWhole`) -/
theorem privacyWhole : Spec.privacyWhole :=
  fun _ _ _ _ W WP p Ryes Rno hsub hwd hC hF hW hG hWP Sm i₀ z hz B hB _ hh =>
    GenMap.privacyWith (via_KE W WP p)
      _ (privacyPubWhole W WP p _ _ Ryes Rno hsub hwd hC hW hG hWP hF Sm i₀ z hz B hB hh)

/-- at the hash terms for one budget of queries -/
theorem privacyWholeTot (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (hsub : ∀ i x, Ryes i x → Rno i x) (hwd : L.Wired) (hC : L.onlineBatch.ann.Coherent)
    (hF : L.onlineBatch.ann.Fmt) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (Sm : Sims L) (i₀ : I)
    (z : ℝ≥0∞)
    (hz : Hiop.HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) (Hiop.simWhole L Sm i₀) z)
    (B : ℕ) (hB : B ≤ L.maxBatchSize) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBKE W WP p) B (simBKGr W p Sm i₀)
      (fun t n => p.leaves * binTail n p.leaves p.s1 + hashTermsBGTot W p t n + z) :=
  privacyWhole I X lam L W WP p Ryes Rno hsub hwd hC hF hW hG hWP Sm i₀ z hz B hB
    _ (hopU_of_hopB hB (hopB_total W p))

/-! ## Part 7. The hypothesis can be met: the run-by-run facts give it -/

/-- the budget of the scheme gives the budget of the whole object at the scheme's bounds -/
theorem starBounds_fits (L : BatchProtocol I X) (p : Params) (M : LH.Nums) (hBu : Budget p M) :
    (Hiop.Star.starBounds L p.leaves p.s1).Fits M.b M.qT M.qpar M.qch M.qon := by
  refine ⟨?_, fun j hj _ => ?_⟩
  · show M.qT + p.leaves * M.qpar + (if (0 : ℕ) = 0 then 0 else p.s1) * M.qon + 0 ≤ M.b
    rw [if_pos rfl, Nat.zero_mul]
    exact hBu.1
  · show M.qch + (if j = 0 then 0 else p.s1) * M.qon + 0 ≤ M.b
    rw [if_neg (by omega)]
    exact hBu.2

theorem starBounds_total (L : BatchProtocol I X) (m s1 : ℕ) :
    (Hiop.Star.starBounds L m s1).total = m * s1 := by
  show ∑ j ∈ Finset.range (m + 1), (if j = 0 then 0 else s1) = m * s1
  rw [Finset.sum_range_succ']
  simp

theorem starBounds_err (L : BatchProtocol I X) (m s1 : ℕ) (zT zL zO : ℝ≥0∞) :
    (Hiop.Star.starBounds L m s1).err zT zL zO =
      zT + m * zL + ((m * s1 : ℕ) : ℝ≥0∞) * (L.maxBatchSize * zO) := by
  unfold Hiop.Bounds.err
  rw [starBounds_total]
  rfl

/-- From the run-by-run facts, through the whole object: the hypotheses of privacyKEGrWithBOf give
HVZKWhole at the scheme's bounds, and so index privacy. -/
theorem privacy_of_runs (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK)
    (hF : L.onlineBatch.ann.Fmt) (hBu : Budget p M) (Sm : Sims L) (hS : Sm.Good Ryes M.zT M.zL M.zO)
    (i₀ : I) (B : ℕ) (hB : B ≤ L.maxBatchSize) {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno h.sub) (argBKE W WP p) B (simBKGr W p Sm i₀)
      (zetaWhole p hb
        (M.zT + p.leaves * M.zL + ((p.leaves * p.s1 : ℕ) : ℝ≥0∞) * (L.maxBatchSize * M.zO))) := by
  rw [← starBounds_err L p.leaves p.s1]
  exact privacyWhole I X lam L W WP p Ryes Rno h.sub h.wired h.cohB hF hW hG hWP Sm i₀ _
    (Hiop.hvzk_whole I X L Ryes M.b M.qT M.qpar M.qch M.qon M.zT M.zL M.zO h.wired h.reads Sm hS _
      (starBounds_fits L p M hBu) i₀)
    B hB hb hh

end Compile.Batch
