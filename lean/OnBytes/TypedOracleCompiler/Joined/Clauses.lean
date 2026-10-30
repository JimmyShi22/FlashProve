-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Clauses.lean: three things that a file's chains do and one chain by itself does
not, as laws of what the compiled verifier does after its chain.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

A file's three chains are the stretches of one protocol, whose shape is a concatenation `s ++ u`
(OnBytes/TypedOracleCompiler/Joined/Cut.lean). After the chain the verifier checks openings (`checksB`) and builds a
transcript from them (`mkTr`); both go round by round and look at one predicate `isRead` on the
positions of ALL rounds. No new verifier is defined here.

  1. A tree taken over. A later stretch's verifier messages may ask for a position of an earlier
     stretch. `treeOf` is the depth and the root of the tree in which a position stands: they come
     from the wire record of the position's OWN round and from the roots that the chain took in that
     round. `mem_checksB`: every position that is read, whoever asked for it, and whose tree has a
     root (`treeOf` is some) is checked against that root. A read position without a root is not
     checked: `mkTr` lays the fixed symbol there. `checked_of_run`: behind a run of the chain from
     its start, at an annotation in which every round has a format (`RoundSplits.Fmt`; a file's is one:
     `Chains.ann_fmt`, Compile/Joined/Ann.lean), every position has its root, so every read position
     is checked. `treeOf_left`: for a
     position of s the tree is a function of the roots taken over s alone. `takenOver_binds`:
     outside the event E_M the symbol that the verifier uses there is the one that the trace
     determines under the roots taken over s (`trStar` at s).
  2. A tree read at two lists. `notOnce_agree`: outside E_M two families of openings that both pass
     their checks against the same roots give the same symbol wherever both are read. (What is read
     is a predicate on positions, so two lists are their union and only membership counts:
     `checksB_append`, `checksB_of_mem_iff`: these two only rewrite the predicate.)
  3. Several roots in one message. The wire records hold a list of depths for each component, and
     the chain takes as many roots as there are depths, at most `maxRt` (`takeRt`). `RtFlagsAll`
     says so of all rounds; `rtFlags_of_runsIn`: it holds of what a run of the chain yields;
     `isSome_treeOf`: then every position of a component that is sent has its tree's root;
     `sentAt_of_runsIn`: at a formatted annotation every position's component is sent.

Limits: nothing here speaks of the chain's queries, of the values that pass from one stretch to the
next, of a bound, or of completeness. `takenOver_binds` and `notOnce_agree` have the hypotheses of
`read_mkTr_eq` (OnBytes/TypedOracleCompiler/Compile/Batch/Runs.lean), on which they rest. Not bound here, though a
file in the byte format has them: the number in a leaf's label and the value of the sender's run in
its salt (in these types an opening's salt is free), and that two pruned sets of paths behind two
lists show one value at a vertex under one root.
No other file of the library uses `checked_of_run`, `takenOver_binds`, `notOnce_agree` or
`mem_checksB` yet.

Terms: lean/GLOSSARY.md.

-/
import Compile.Joined.Ann
import OnBytes.TypedOracleCompiler.Joined.Cut
import OnBytes.TypedOracleCompiler.Compile.Batch.Runs

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The tree of a position -/

/-- depth and root number k of a component with the depths ds and the roots rt; none if either list
ends before k -/
def treeAt (ds : List ℕ) (rt : List (Dig lam)) (k : ℕ) : Option (ℕ × Dig lam) :=
  match ds[k]?, rt[k]? with
  | some d, some c => some (d, c)
  | _, _ => none

/-- The depth and the root of the tree in which a position stands: from the wire record of the
position's own round and the roots that the chain has taken in that round. none: its component is
not sent, or has no such tree. -/
def treeOf : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s → OPos s →
    Option (ℕ × Dig lam)
  | _ :: _, (a, _), (w, _), (rt, _), .inl p =>
      if a.own p then treeAt w.depthJ (rt.2.getD []) (w.tree p)
      else treeAt w.depth0 (rt.1.getD []) (w.tree p)
  | _ :: s, (_, A), (_, W), (_, R), .inr p => treeOf s A W R p

/-- the number of the leaf at which a position stands in its tree -/
def placeOf : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → OPos s → ℕ
  | _ :: _, (_, _), (w, _), .inl p => w.place p
  | _ :: s, (_, A), (_, W), .inr p => placeOf s A W p

theorem treeAt_eq_some {ds : List ℕ} {rt : List (Dig lam)} {k d : ℕ} {c : Dig lam}
    (h : treeAt ds rt k = some (d, c)) : ds[k]? = some d ∧ rt[k]? = some c := by
  unfold treeAt at h
  cases h1 : ds[k]? with
  | none => rw [h1] at h; cases h
  | some d' =>
    cases h2 : rt[k]? with
    | none => rw [h1, h2] at h; cases h
    | some c' => rw [h1, h2] at h; cases h; exact ⟨rfl, rfl⟩

/-- One component: a read position whose tree has a depth and a root has an opening, and its check,
against that root, is among the checks. -/
theorem mem_checksOpt {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) {cs : List (Check lam L)}
    (hcs : checksOpt posAt depth emb rt isRead f = some cs) (p : r.Pos) {k j d : ℕ} {c : Dig lam}
    (ht : treeAt depth rt k = some (d, c)) (hj : j < 2 ^ d) (hpos : posAt k j = some p)
    (hr : isRead p = true) :
    ∃ op, f p = some op ∧ (⟨⟨emb p op.sym, op.salt⟩, j, op.path, c, d⟩ : Check lam L) ∈ cs := by
  obtain ⟨hd, hc⟩ := treeAt_eq_some ht
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hcs
  obtain ⟨cs', h1, h2⟩ := mem_checksTrees posAt emb isRead f 0 depth rt l hl k d c hd hc
  rw [Nat.zero_add] at h1
  obtain ⟨op, hop, hmem⟩ :=
    mem_checksComp (posAt k) d emb c isRead f _ cs' h1 j (List.mem_range.2 hj) p hpos hr
  exact ⟨op, hop, List.mem_flatMap.2 ⟨_, h2, hmem⟩⟩

/-- Every position that is read and whose tree has a root has an opening, and its check is among the
checks: at the position's leaf, against the root that the chain took in the position's own round,
at the depth that the wire record of that round gives. Why the position is read plays no part. -/
theorem mem_checksB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (emb : (p : OPos s) → OSym s p → Body L) (R : RootsOfChain lam s) (isRead : OPos s → Bool)
          (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
        checksB s A W emb R isRead f = some cs →
        ∀ (p : OPos s) (d : ℕ) (c : Dig lam), isRead p = true → treeOf s A W R p = some (d, c) →
          ∃ op, f p = some op ∧
            (⟨⟨emb p op.sym, op.salt⟩, placeOf s A W p, op.path, c, d⟩ : Check lam L) ∈ cs
  | [], _, _, _, _, _, _, _, _, _, p, _, _, _, _ => nomatch p
  | r :: s, (a, A), (w, W), hW, emb, (rt, R), isRead, f, cs, hcs, p, d, c, hr, ht => by
      simp only [checksB] at hcs
      cases h0 : checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
      | none => rw [h0] at hcs; cases hcs
      | some c0 =>
        cases hJ : checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
            (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
        | none => rw [h0, hJ] at hcs; cases hcs
        | some cJ =>
          cases h2 : checksB s A W (fun p => emb (.inr p)) R
              (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
          | none => rw [h0, hJ, h2] at hcs; cases hcs
          | some c2 =>
            rw [h0, hJ, h2] at hcs
            cases hcs
            match p, hr, ht with
            | .inl q, hr, ht =>
              by_cases ho : a.own q = true
              · have ht' : treeAt w.depthJ (rt.2.getD []) (w.tree q) = some (d, c) := by
                  simpa only [treeOf, ho, if_true] using ht
                obtain ⟨d', hd', hlt⟩ := hW.1.place_ltJ q ho
                obtain rfl : d' = d := Option.some.inj (hd'.symm.trans (treeAt_eq_some ht').1)
                obtain ⟨op, hop, hm⟩ := mem_checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p))
                  (rt.2.getD []) _ _ hJ q ht' hlt (hW.1.posAtJ_place q ho) hr
                exact ⟨op, hop, List.mem_append_left _ (List.mem_append_right _ hm)⟩
              · have ho' : a.own q = false := by simpa using ho
                have ht' : treeAt w.depth0 (rt.1.getD []) (w.tree q) = some (d, c) := by
                  simpa only [treeOf, ho', Bool.false_eq_true, if_false] using ht
                obtain ⟨d', hd', hlt⟩ := hW.1.place_lt0 q ho'
                obtain rfl : d' = d := Option.some.inj (hd'.symm.trans (treeAt_eq_some ht').1)
                obtain ⟨op, hop, hm⟩ := mem_checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p))
                  (rt.1.getD []) _ _ h0 q ht' hlt (hW.1.posAt0_place q ho') hr
                exact ⟨op, hop, List.mem_append_left _ (List.mem_append_left _ hm)⟩
            | .inr q, hr, ht =>
              obtain ⟨op, hop, hm⟩ := mem_checksB s A W hW.2 (fun p => emb (.inr p)) R
                (fun p => isRead (.inr p)) (fun p => f (.inr p)) c2 h2 q d c hr ht
              exact ⟨op, hop, List.mem_append_right _ hm⟩

/-! ## 1. A tree taken over -/

/-- The tree of a position of s, in `s ++ u`: a function of the wire records of s and of the roots
taken over s. -/
theorem treeOf_left : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (R : RootsOfChain lam (s ++ u)) (p : OPos s),
    treeOf (s ++ u) (RoundSplits.app A B) W R (OPos.left p) = treeOf s A (WireSB.fst W) (RT.fst R) p
  | _ :: _, _, (_, _), _, (_, _), (_, _), .inl _ => rfl
  | _ :: _, _, (_, _), _, (_, W), (_, R), .inr p => treeOf_left W R p

/-- The tree of a position of u, in `s ++ u`. -/
theorem treeOf_right : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (R : RootsOfChain lam (s ++ u)) (p : OPos u),
    treeOf (s ++ u) (RoundSplits.app A B) W R (OPos.right (s := s) p) =
      treeOf u B (WireSB.snd W) (RT.snd (s := s) R) p
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (_, W), (_, R), p => treeOf_right W R p

theorem placeOf_left : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (p : OPos s),
    placeOf (s ++ u) (RoundSplits.app A B) W (OPos.left p) = placeOf s A (WireSB.fst W) p
  | _ :: _, _, (_, _), _, (_, _), .inl _ => rfl
  | _ :: _, _, (_, _), _, (_, W), .inr p => placeOf_left W p

theorem placeOf_right : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (p : OPos u),
    placeOf (s ++ u) (RoundSplits.app A B) W (OPos.right (s := s) p) = placeOf u B (WireSB.snd W) p
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (_, W), p => placeOf_right W p

/-- how a leaf's body is read back as a symbol, at the positions of s -/
def prjLeft {s u : Shape} (prjS : (p : OPos (s ++ u)) → Body L → Option (OSym (s ++ u) p)) :
    (p : OPos s) → Body L → Option (OSym s p) :=
  fun p b => (prjS (OPos.left p) b).map (OSym.ofLeft p)

/-- the same at the positions of u -/
def prjRight {s u : Shape} (prjS : (p : OPos (s ++ u)) → Body L → Option (OSym (s ++ u) p)) :
    (p : OPos u) → Body L → Option (OSym u p) :=
  fun p b => (prjS (OPos.right (s := s) p) b).map (OSym.ofRight (s := s) p)

/-- The first part of the transcript that the trace determines under the roots taken over `s ++ u`
is the transcript that it determines under the roots taken over s. -/
theorem trStar_fst (tr : Trace (typedOracleFamily lam K L)) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
    (prjS : (p : OPos (s ++ u)) → Body L → Option (OSym (s ++ u) p)) (R : RootsOfChain lam (s ++ u))
    (pls : Plains (s ++ u)) (ρ : Rho (s ++ u)),
    Tr.fst (trStar tr (s ++ u) (RoundSplits.app A B) W prjS R pls ρ) =
      trStar tr s A (WireSB.fst W) (prjLeft prjS) (RT.fst R) (Plains.fst pls) (Rho.fst ρ)
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: s, u, (a, A), B, (w, W), prjS, (rt, R), (pl, pls), (c, ρ) => by
      have e : (fun p => prjLeft (s := r :: s) (u := u) prjS (.inl p)) =
          fun p => prjS (.inl p) := by
        funext p b
        exact Option.map_id'
      show (msgStar tr w (fun p => prjS (.inl p)) rt pl, c, Tr.fst (trStar tr (s ++ u)
          (RoundSplits.app A B) W (fun p => prjS (.inr p)) R pls ρ)) =
        (msgStar tr w (fun p => prjLeft (s := r :: s) (u := u) prjS (.inl p)) rt pl, c,
          trStar tr s A (WireSB.fst W) (fun p => prjLeft (s := r :: s) (u := u) prjS (.inr p))
            (RT.fst R) (Plains.fst pls) (Rho.fst ρ))
      rw [e, trStar_fst tr W (fun p => prjS (.inr p)) R pls ρ]
      rfl

/-- The second part likewise: under the roots taken over u. -/
theorem trStar_snd (tr : Trace (typedOracleFamily lam K L)) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
    (prjS : (p : OPos (s ++ u)) → Body L → Option (OSym (s ++ u) p)) (R : RootsOfChain lam (s ++ u))
    (pls : Plains (s ++ u)) (ρ : Rho (s ++ u)),
    Tr.snd (s := s) (trStar tr (s ++ u) (RoundSplits.app A B) W prjS R pls ρ) =
      trStar tr u B (WireSB.snd W) (prjRight (s := s) prjS) (RT.snd (s := s) R)
        (Plains.snd (s := s) pls) (Rho.snd (s := s) ρ)
  | [], u, _, B, W, prjS, R, pls, ρ => by
      have e : prjRight (s := []) (u := u) prjS = prjS := by
        funext p b
        exact Option.map_id'
      show trStar tr u B W prjS R pls ρ = trStar tr u B W (prjRight (s := []) (u := u) prjS) R pls ρ
      rw [e]
  | _ :: _, _, (_, _), _, (_, W), prjS, (_, R), (_, pls), (_, ρ) =>
      trStar_snd tr W (fun p => prjS (.inr p)) R pls ρ

section Binds
variable {tr : Trace (typedOracleFamily lam K L)}

/-- **A tree taken over.** Outside E_M, if the checks of the verifier over `s ++ u` pass, then at
every position of s that is read, for whatever reason (say, because verifier messages of u ask for
it), the transcript that the verifier builds holds the symbol that the trace determines under the
roots that the chain took over s. The trace is the whole trace: this says WHAT it determines under
those roots, not WHEN; that the symbol stood already when the round of s was hashed is not said
here. -/
theorem takenOver_binds (hM : ¬ EM tr) {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (hco : (RoundSplits.app A B).Coherent) (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B))
    (hW : RoundsQueryLayout.OKG (s ++ u) (RoundSplits.app A B) W)
    (embS : (p : OPos (s ++ u)) → OSym (s ++ u) p → Body L)
    (prjS : (p : OPos (s ++ u)) → Body L → Option (OSym (s ++ u) p))
    (hprj : ∀ p x, prjS p (embS p x) = some x) (R : RootsOfChain lam (s ++ u))
    (isRead : OPos (s ++ u) → Bool)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))) (cs : List (Check lam L))
    (hcs : checksB (s ++ u) (RoundSplits.app A B) W embS R isRead f = some cs)
    (hall : ∀ c ∈ cs, c.wellFormed = true ∧ RunsIn tr (runCheck (K := K) c) true)
    (pls : Plains (s ++ u)) (ρ : Rho (s ++ u)) (p : OPos s) (hr : isRead (OPos.left p) = true) :
    OSym.ofLeft p ((mkTr (s ++ u) (RoundSplits.app A B) W R pls ρ f).read (OPos.left p)) =
      (trStar tr s A (WireSB.fst W) (prjLeft prjS) (RT.fst R) (Plains.fst pls)
        (Rho.fst ρ)).read p := by
  rw [read_mkTr_eq hM (s ++ u) (RoundSplits.app A B) hco W hW embS prjS hprj R isRead f cs hcs hall pls ρ
    (OPos.left p) hr, Tr.read_left, trStar_fst]

/-! ## 2. A tree read at two lists -/

/-- **Two openings of one place agree.** Outside E_M, two families of openings that pass their
checks against the same roots, each for its own set of read positions, give the same symbol at every
position that is read in both. -/
theorem notOnce_agree (hM : ¬ EM tr) (s : Shape) (A : RoundSplits s) (hco : A.Coherent)
    (W : RoundsQueryLayout lam K s A) (hW : RoundsQueryLayout.OKG s A W) (embS : (p : OPos s) → OSym s p → Body L)
    (prjS : (p : OPos s) → Body L → Option (OSym s p)) (hprj : ∀ p x, prjS p (embS p x) = some x)
    (R : RootsOfChain lam s) (isRead isRead' : OPos s → Bool)
    (f f' : (p : OPos s) → Option (Opening lam (OSym s p))) (cs cs' : List (Check lam L))
    (hcs : checksB s A W embS R isRead f = some cs)
    (hcs' : checksB s A W embS R isRead' f' = some cs')
    (hall : ∀ c ∈ cs, c.wellFormed = true ∧ RunsIn tr (runCheck (K := K) c) true)
    (hall' : ∀ c ∈ cs', c.wellFormed = true ∧ RunsIn tr (runCheck (K := K) c) true)
    (pls : Plains s) (ρ : Rho s) (p : OPos s) (hr : isRead p = true) (hr' : isRead' p = true) :
    (mkTr s A W R pls ρ f).read p = (mkTr s A W R pls ρ f').read p := by
  rw [read_mkTr_eq hM s A hco W hW embS prjS hprj R isRead f cs hcs hall pls ρ p hr,
    read_mkTr_eq hM s A hco W hW embS prjS hprj R isRead' f' cs' hcs' hall' pls ρ p hr']

end Binds

/-- Of a list of read positions only membership counts: neither order nor repetition. -/
theorem checksB_of_mem_iff {s : Shape} (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L) (R : RootsOfChain lam s) [DecidableEq (OPos s)]
    {l l' : List (OPos s)} (h : ∀ p, p ∈ l ↔ p ∈ l')
    (f : (p : OPos s) → Option (Opening lam (OSym s p))) :
    checksB s A W emb R (fun p => decide (p ∈ l)) f =
      checksB s A W emb R (fun p => decide (p ∈ l')) f := by
  have e : (fun p => decide (p ∈ l)) = fun p => decide (p ∈ l') :=
    funext fun p => decide_eq_decide.2 (h p)
  rw [e]

/-- Two lists of read positions are read as their union. -/
theorem checksB_append {s : Shape} (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L) (R : RootsOfChain lam s) [DecidableEq (OPos s)]
    (l l' : List (OPos s)) (f : (p : OPos s) → Option (Opening lam (OSym s p))) :
    checksB s A W emb R (fun p => decide (p ∈ l ++ l')) f =
      checksB s A W emb R (fun p => decide (p ∈ l) || decide (p ∈ l')) f := by
  have e : (fun p => decide (p ∈ l ++ l')) = fun p => decide (p ∈ l) || decide (p ∈ l') :=
    funext fun p => by simp only [List.mem_append, Bool.decide_or]
  rw [e]

/-! ## 3. Several roots in one message -/

/-- In every round a component that is sent has as many roots as it has trees, and at most
`maxRt`. -/
def RtFlagsAll : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → RootsOfChain lam s → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), (rt, R) => RtFlags w rt ∧ RtFlagsAll s A W R

/-- What a run of the chain yields has as many roots as the wire records have trees. -/
theorem rtFlags_of_runsIn {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      RtFlagsAll s A W R
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, _, _, ph', _, (_, pls), (_, ρ), (_, R), h => by
      obtain ⟨_, _, ph₁, rts', _, _, _, h', hfl⟩ := runsIn_chainB_cons_flags h
      exact ⟨hfl, rtFlags_of_runsIn s A W _ _ ph₁ ph' rts' pls ρ R h'⟩

theorem rtFlags_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K (s ++ u) (RoundSplits.app A B)) (R : RootsOfChain lam (s ++ u)),
    RtFlagsAll (s ++ u) (RoundSplits.app A B) W R ↔
      RtFlagsAll s A (WireSB.fst W) (RT.fst R) ∧ RtFlagsAll u B (WireSB.snd W) (RT.snd (s := s) R)
  | [], _, _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, _), _, (_, W), (_, R) =>
    have h := rtFlags_app W R
    ⟨fun z => ⟨⟨z.1, (h.1 z.2).1⟩, (h.1 z.2).2⟩, fun z => ⟨z.1.1, h.2 ⟨z.1.2, z.2⟩⟩⟩

/-- is the component of this position sent, by what the chain has yielded -/
def sentAt : (s : Shape) → (A : RoundSplits s) → RootsOfChain lam s → OPos s → Bool
  | _ :: _, (a, _), (rt, _), .inl p => if a.own p then rt.2.isSome else rt.1.isSome
  | _ :: s, (_, A), (_, R), .inr p => sentAt s A R p

/-- With lawful wire records and as many roots as trees, every position of a component that is sent
has the root of its tree, whichever of the component's trees that is. -/
theorem isSome_treeOf :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (R : RootsOfChain lam s), RtFlagsAll s A W R → ∀ p : OPos s, sentAt s A R p = true →
        (treeOf s A W R p).isSome = true
  | [], _, _, _, _, _, p, _ => nomatch p
  | _ :: _, (a, _), (w, _), hW, (rt, _), hR, .inl q, hs => by
      by_cases ho : a.own q = true
      · obtain ⟨d, hd, -⟩ := hW.1.place_ltJ q ho
        simp only [sentAt, ho, if_true] at hs
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
        have hlt : w.tree q < x.length := by
          rw [(hR.1.2 x hx).1]
          exact (List.getElem?_eq_some_iff.1 hd).1
        simp only [treeOf, ho, if_true, treeAt, hd, hx, Option.getD_some,
          List.getElem?_eq_getElem hlt, Option.isSome_some]
      · have ho' : a.own q = false := by simpa using ho
        obtain ⟨d, hd, -⟩ := hW.1.place_lt0 q ho'
        simp only [sentAt, ho', Bool.false_eq_true, if_false] at hs
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
        have hlt : w.tree q < x.length := by
          rw [(hR.1.1 x hx).1]
          exact (List.getElem?_eq_some_iff.1 hd).1
        simp only [treeOf, ho', Bool.false_eq_true, if_false, treeAt, hd, hx, Option.getD_some,
          List.getElem?_eq_getElem hlt, Option.isSome_some]
  | _ :: s, (_, A), (_, W), hW, (_, R), hR, .inr q, hs => isSome_treeOf s A W hW.2 R hR.2 q hs

/-! ## Every position of a file has its root -/

/-- the phase of a chain without its values -/
def fph : Phase lam → FPhase
  | .first => .first
  | .loc _ => .loc
  | .shr _ _ => .shr
  | .aft _ _ => .aft

/-- One round of the chain at a formatted annotation: every position's component is sent, and the
rest is formatted from the next phase on. -/
theorem sent_of_vstep {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {r : Round} {s : Shape} {a : RAnn r}
    {A : RoundSplits s} {cms : List (Dig lam)} {x : Option X} {salt : Bits} {rtreq : Dig lam}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {pl : r.Plain}
    {ph ph₁ : Phase lam} {cur : Item lam L t} {ans : FsAns lam K} {rt : RtC lam × RtC lam}
    (hv : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    (hF : RoundSplits.FmtFrom (r :: s) (a, A) (fph ph)) :
    (∀ q, (if a.own q then rt.2.isSome else rt.1.isSome) = true) ∧ RoundSplits.FmtFrom s A (fph ph₁) := by
  cases hv with
  | f1 root ans hk =>
    simp only [RoundSplits.FmtFrom, hk] at hF
    exact ⟨fun q => by rw [hF.1.1 q]; rfl, hF.2⟩
  | f2 ρ root ans hk =>
    simp only [RoundSplits.FmtFrom, hk] at hF
    exact ⟨fun q => by rw [hF.1.1 q]; rfl, hF.2⟩
  | join ρ rtj rt0 c ans hk hg =>
    simp only [RoundSplits.FmtFrom, hk, fph] at hF
    exact ⟨fun q => by cases a.own q <;> rfl, hF⟩
  | f5 ρ0 c root ans hk =>
    simp only [RoundSplits.FmtFrom, hk, fph] at hF
    exact ⟨fun q => by rw [hF.1.1 q]; rfl, hF.2⟩
  | f3 ρ0 c root ans hk =>
    simp only [RoundSplits.FmtFrom, hk] at hF
    exact ⟨fun q => by rw [hF.1.1 q]; rfl, hF.2⟩
  | f2' ρ c root ans hk =>
    simp only [RoundSplits.FmtFrom, hk] at hF
    exact ⟨fun q => by rw [hF.1.1 q]; rfl, hF.2⟩

/-- Behind a run of the chain at a formatted annotation every position's component is sent. -/
theorem sentAt_of_runsIn {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      RoundSplits.FmtFrom s A (fph ph) →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      ∀ p : OPos s, sentAt s A R p = true
  | [], _, _, _, _, _, _, _, _, _, _, _, _, p => nomatch p
  | _ :: s, (_, A), (_, W), _, _, _, ph', _, (_, pls), (_, ρ), (_, R), hF, h, p => by
      obtain ⟨_, _, ph₁, rts', hv, _, _, h', _⟩ := runsIn_chainB_cons_flags h
      obtain ⟨h1, h2⟩ := sent_of_vstep hv hF
      match p with
      | .inl q => exact h1 q
      | .inr q => exact sentAt_of_runsIn s A W _ _ ph₁ ph' rts' pls ρ R h2 h' q

/-- **Every read position is checked.** Behind a run of the chain from its start, at a formatted
annotation and lawful wire records: every position that is read has an opening, and its check,
against the root that the chain took in the position's own round, is among the checks. -/
theorem checked_of_run {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {s : Shape} {A : RoundSplits s} (hF : A.Fmt)
    {W : RoundsQueryLayout lam K s A} (hW : RoundsQueryLayout.OKG s A W) {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)}
    {i : ℕ} {ph' : Phase lam} {rts : List (Dig lam)} {pls : Plains s} {ρ : Rho s} {R : RootsOfChain lam s}
    (hrun : RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i .first rts pls)
      (some (ρ, R, ph')))
    {emb : (p : OPos s) → OSym s p → Body L} {isRead : OPos s → Bool}
    {f : (p : OPos s) → Option (Opening lam (OSym s p))} {cs : List (Check lam L)}
    (hcs : checksB s A W emb R isRead f = some cs) (p : OPos s) (hr : isRead p = true) :
    ∃ d c op, treeOf s A W R p = some (d, c) ∧ f p = some op ∧
      (⟨⟨emb p op.sym, op.salt⟩, placeOf s A W p, op.path, c, d⟩ : Check lam L) ∈ cs := by
  have hs := isSome_treeOf s A W hW R (rtFlags_of_runsIn s A W embP i .first ph' rts pls ρ R hrun) p
    (sentAt_of_runsIn s A W embP i .first ph' rts pls ρ R hF hrun p)
  obtain ⟨⟨d, c⟩, ht⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨op, hop, hm⟩ := mem_checksB s A W hW emb R isRead f cs hcs p d c hr ht
  exact ⟨d, c, op, ht, hop, hm⟩

end TypedOracleCompiler.Joined
