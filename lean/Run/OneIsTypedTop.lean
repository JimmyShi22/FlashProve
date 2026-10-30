-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTypedTop.lean: the run of the compiled verifier over a single oracle and its run at typed
oracle functions give the same outcome on every proof file, for every description that passes two
tests and four bounds on numbers.

The generic construction takes a description S of a protocol's rounds and yields a compiled
verifier: the verifier of the non-interactive argument that the compiler makes of the protocol
(Merkle trees, a hash chain for the challenges; `Compile.Batch.verifyOneProtocol`; proof of work is tested
where the protocol's `accept` tests it, as here (`passSL` in `PSof`, Run/PlanQS.lean)). It can be
run in two ways. In the first (`run1C`, Run/PageQRunC.lean) the verifier has a single oracle on bit
strings: every query is encoded as a bit string, and all output blocks of the oracle are requested,
also those that the format never uses. In the second (`runLaxC`, Run/PlanQS.lean) the verifier is
given one oracle function for each kind of query (chain, leaf, node), each defined directly from the
hash calls of the format page (docs/format/FORMAT.md, which comes with the programs, the C++
implementation that comes with this Lean code; this file has not been held against the page as it
ships, and may differ from it),
as rendered in Fmt/Rules23.lean. An outcome says who
decided (the file reader or the verifier) as well as what was decided.

Sources. Written against the leaf's label in the format page (FORMAT.md, R2.1; Fmt/Rules23.lean,
leafPlace); this file has not been held against the page as it ships, and may differ from it.


1. What the file contains.
   `FitsS S K`; `fourBounds S K`.

2. What is checked when the file compiles. Two tests (#guard): `ok`, `OKQ` and `fourBounds` hold for
   the two descriptions at the programs' own parameters (Fmt/M1TheirsSpec.lean).

3. Theorems.
   `one_is_typed`: `ok S = true`, `OKQ S = true`, K + 1 < 2^48, `S.statement.size < 2^64`,
     `S.rounds.length < 2^64` and `S.firstTree + nRoots S ≤ 2^48` imply
     `run1C S C K chal dec file = runLaxC S C K chal dec file`. Here C fixes the types of the
     verifier's challenges, K is the number of blocks that `chal` reads (the verifier is run at
     `K + 1` message blocks), chal turns blocks into challenges, and dec is the protocol's decision.
   `one_is_typedB`: The same, with the four bounds as the one test `fourBounds`.
   `one_pull`: `ok S = true`, `OKQ S = true` and `fourBounds S (kOf S) = true` imply
     `run1PF S dec file = runLaxSP S dec file`. This is the equation at one of the two choices of C
     that the runs in this folder use. That choice is challenges as hash blocks (`ckP`,
     Run/PlanPull.lean; "pull" in names). With it a round's verifier message is the round's 256-bit
     blocks themselves, and reads and decision apply the sampling rule. `runLaxSP` is in
     Run/PlanQSP.lean, `run1PF` in Run/PageQKeepC.lean. By the tests in the files that run them,
     their runs at the toys' full parameters finish.
   `one_ck`: Under the same three hypotheses, `run1K S dec file = runLaxS S dec file`. This is the
     equation at the other choice, challenges as sampled values (`ck`, Run/PlanDrawsQ.lean): the
     values that the format draws, field elements and positions among them. `runLaxS` is in
     Run/PlanQS.lean, `run1K` in Run/PageQKeep.lean.
   How it is proved. For `OKQ S = true`, Run/OneIsTyped.lean has the equation (`one_file`) for every
   file that passes a test ("on what the lenient reader, which only splits the file, makes of it,
   the verifier asks no query that the encoding cannot write"). To cut the file, the lenient reader
   recomputes the hash chain, and it refuses some files (what it still asks the hash, what it
   refuses and what it does not test: part 1 of the head of Run/ParseLax.lean). Here, under the
   hypotheses of `one_is_typed`, that test is proved to hold for every file, in three steps.
     `asked_of`: The test (`askedQ .. = true`) holds for an argument string (the proof, as the
       compiler's theorems type it) with a first salt of 256 bits and nonces below 2^64, if
       `OKQ S = true` and `FitsS S K`. (That the chain never joins (all rounds are local), and the
       form of the leaf queries: Run/ThinAskedMore.lean.)
     `parse_facts`: For `ok S = true`, what the lenient reader, run at the format's hash, returns is
       such a string.
     `fitsS_of`: Within the construction's limits (`PQ.ok S`), `FitsS S K` follows from the four
       bounds.
   Why the bounds. K + 1 < 2^48: a call's number has 48 bits in its word; beyond that the encoding
   does not write a round's query in the format, and the two families of oracle functions differ.
   The others: a round's number, the statement's length and the word that holds a tree's number must
   each fit into a word. By the format page as this file reads it,
   that word also holds the numbers of a column's words and of a salt's words
   (Fmt/Rules23.lean, leafPlace). That each of the three keeps
   to its place, so that two trees' words differ, follows from the format's own conditions on a
   description (Fmt/Rules8Ok.lean: `ok_count`, `ok_small`, `ok_salt`; a tree that is opened nowhere
   gets the shape `bareShape`, Run/PlanQTypes.lean, with one word a column), not from the fourth
   bound. Under `ok S = true` the fourth bound follows from `ok_count`. The first three bounds are
   what the encoding needs (`FitsS`: `k48`, `stm`, `len`). The bounds are wider than the format
   page's own bounds (FORMAT.md, R2.3, R2.7): `fourBounds` is not a test of the format page.

4. What is not claimed.
   Nothing about runs behind the strict reader.
   Nothing here about the run functions with whole paths (each opened leaf has an authentication
   path of its own): for them see Run/OneIsTypedFull.lean (`Spec.oneW_is_typed`).
   No statement on soundness follows. Neither run is shown here to be the verifier of the scheme in
   the soundness theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.ThinAskedMore
import Run.OneIsTypedChain
import Run.OneIsTypedLeaf
import Run.PageIsReaders
import Run.PageIsTopProofs
import Run.PageIsTabProofs
import Run.PlanQSP
import Fmt.M1TheirsSpec
import Fmt.Rules8Ok

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Thin Run.Twin
open _root_.Fmt (Item RoundOut ChainOut)

/-- What is asked of a description and the number of blocks. -/
structure FitsS (S : _root_.Fmt.Spec) (K : ℕ) : Prop where
  k48   : K + 1 < 2 ^ 48
  work  : ∀ r ∈ S.rounds, r.entry.work < 256
  stm   : S.statement.size < 2 ^ 64
  roots : RootsFit (rds S)
  len   : (rds S).length < 2 ^ 64
  num   : Numbered S.firstTree (rds S)
  small : SmallTrees (rds S)
  salt  : S.plan.salt / 8 < 2 ^ 8

section
variable (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : View → Bool) (h : OKQ S = true)

theorem kindQ_lt (i : ℕ) : (chainQ S C dec).kind i < 256 := by
  show (if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7) < 256
  split
  · omega
  · cases S.rounds[i - 1]? with
    | none => show 7 < 256; omega
    | some r =>
      show r.kind.num < 256
      cases r.kind <;> simp [_root_.Fmt.Kind.num]

theorem workQ_lt (hw : ∀ r ∈ S.rounds, r.entry.work < 256) (i : ℕ) :
    (chainQ S C dec).work i < 256 := by
  show (if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0) < 256
  split
  · omega
  · cases hr : S.rounds[i - 1]? with
    | none => show 0 < 256; omega
    | some r => exact hw r (List.mem_of_getElem? hr)

/-- Under `h` (`OKQ S = true`) and `FitsS S K` (`F`): on a string with a first salt of 256 bits
(`hs`) and nonces below 2^64 (`hn`) the verifier asks nothing off the plan (`askedQ .. = true`). -/
theorem asked_of (F : FitsS S K) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (hs : π.salt.length = 256) (hn : noncesOK C (rds S) π.plains.2) :
    askedQ S C K chal dec h cm π = true := by
  unfold askedQ askedP
  rw [Bool.and_eq_true]
  refine ⟨askP_all S C K chal dec h _ cm π.salt F.k48 (kindQ_lt S C dec) (workQ_lt S C dec F.work)
      hs F.stm F.roots F.len π.roots π.plains.2 hn,
    ?_⟩
  cases hc : chainP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec)
      (gQ S C dec (K + 1) h) id none .onl [cm] (some () : Option Unit) π.salt π.rtreq
      (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh
      (embPS C (rds S) dec) 0 .first π.roots π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    show (!strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec)
          (wqS C K chal (rds S) dec) 0 () π ρ rts ph || _) = true
    by_cases hst : strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec)
        (wqS C K chal (rds S) dec) 0 () π ρ rts ph = true
    · rw [hst, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have := chainP_local (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h) id none .onl [cm]
          (some () : Option Unit) π.salt π.rtreq (SOf C (rds S)) (wqS C K chal (rds S) dec).sh
          (embPS C (rds S) dec) 0 .first π.roots π.plains (ρ, rts, ph) rfl hc
        rw [show ph.slotVal = none from this]
        rfl
      · cases hf : forestsOfP (fun _ => LbS C (rds S) dec) (PSof C (rds S) dec)
            (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
            (fun s => some (.inl s)) [cm] () π ρ rts with
        | none => rfl
        | some Fs =>
          show ((flatP (fun _ => LbS C (rds S) dec) Fs).all fun c => fitLeaf S C K dec h c.inp) =
            true
          rw [List.all_eq_true]
          intro c hcm
          obtain ⟨p, a, salt, e1, e2⟩ :=
            forestsOfP_inp (fun _ => LbS C (rds S) dec) (256 + 8 * S.plan.salt)
              256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) _ _ 0 [cm] ()
              π ρ rts ph hst rfl Fs hf c hcm
          rw [e1]
          exact leaf_fits S C K dec h S.firstTree F.num F.small F.salt p a salt e2
    · rw [Bool.not_eq_true] at hst
      rw [hst]
      rfl

end

/-! ### What the lenient parser's strings are -/

theorem trace_nonce (h : HId) (P : _root_.Fmt.Plan) :
    ∀ (rs : List _root_.Fmt.Round)
        (ros : List RoundOut) (c : _root_.Fmt.Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → ∀ ro ∈ ros, ro.nonce < 2 ^ 64
  | [], [], _, _, _, _, hm => by cases hm
  | [], _ :: _, _, _, ht, _, _ => ht.elim
  | _ :: _, [], _, _, ht, _, _ => ht.elim
  | r :: rs, ro :: ros, c, roots, ht, ro', hm => by
      obtain ⟨h1, -, -, -, -, h6⟩ := ht
      rcases List.mem_cons.1 hm with rfl | hm
      · simp only [_root_.Fmt.askOK, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact h1.1.1.2
      · exact trace_nonce h P rs ros _ _ h6 ro' hm

theorem nonces_of (C : CK) :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)),
      plainsSL C ds ros = some pl → (∀ ro ∈ ros, ro.nonce < 2 ^ 64) → noncesOK C ds pl
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => by cases h
  | d :: ds, o :: os, pl, h, hn => by
      simp only [plainsSL] at h
      split at h
      · rename_i p r e1 e2
        rw [← Option.some.inj h]
        refine ⟨?_, nonces_of C ds os r e2 fun ro hr => hn ro (List.mem_cons_of_mem _ hr)⟩
        show nonceOK d.entry.work (GPlain.mk d.entry.work p o.nonce)
        cases d.entry.work with
        | zero => trivial
        | succ w => exact hn o List.mem_cons_self
      · cases h

/-- For `ok S = true` (`hok`), the lenient parser's string: a first salt of 256 bits, nonces below
2^64. -/
theorem parse_facts (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (hok : ok S = true)
    (file : ByteArray) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (e : parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file =
      some ([cm], π)) :
    π.salt.length = 256 ∧ noncesOK C (rds S) π.plains.2 := by
  have e' : (laxWhole (m := Id) _root_.Fmt.formatHash S file : Option ChainOut).bind
        (toBPrfP (PSof C (rds S) dec) (TYS S C dec)) =
      some ([cm], π) := e
  cases ho : (laxWhole (m := Id) _root_.Fmt.formatHash S file : Option ChainOut) with
  | none => rw [ho] at e'; cases e'
  | some o =>
    rw [ho] at e'
    have hf : LaxFacts _root_.Fmt.formatHash S o :=
      pi_facts _root_.Fmt.formatHash (fun n t i s b => _root_.Fmt.size_H n t i s b) S file o hok ho
    obtain ⟨run, pl, hr, hpl, ht⟩ := pi_typed' _root_.Fmt.formatHash S C dec o hf
    have e2 : ([cm], π) =
        ([bytesToDig o.pd],
          mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o)) :=
      Option.some.inj (e'.symm.trans ht)
    have e3 : π =
        mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o) :=
      (Prod.mk.inj e2).2
    obtain ⟨rnd, -, hrun⟩ := hf.run
    have hsz : run.size = 32 := by
      have : run = _root_.Fmt.formatHash 172 0 S.label _root_.Fmt.zero32 (o.pd ++ rnd) :=
        Option.some.inj (hr.symm.trans hrun)
      rw [this]
      exact _root_.Fmt.size_H _ _ _ _ _
    rw [e3]
    refine ⟨?_,
      nonces_of C (rds S) o.rounds.toList pl hpl
        (trace_nonce _root_.Fmt.formatHash S.plan S.rounds o.rounds.toList _ _ hf.trace)⟩
    show (bytesToBits run).length = 256
    rw [length_bytesToBits, hsz]

/-! ### What a description within the limits gives -/

theorem toRoots_some :
    ∀ (l : List Item) (rt : Option (Dig 256)),
      _root_.Fmt.countItem .root l = (if rt.isSome then 1 else 0) → (toRoots l rt).isSome = true
  | [], none, _ => rfl
  | [], some _, h => by simp [_root_.Fmt.countItem] at h
  | .root :: l, some r, h => by
      have h' : _root_.Fmt.countItem .root l = 0 := by
        simp [_root_.Fmt.countItem] at h ⊢
        exact h
      have := toRoots_some l none (by rw [h']; rfl)
      show ((toRoots l none).map fun y => ((r, y) : Dig 256 × RootOf l)).isSome = true
      rw [Option.isSome_map]
      exact this
  | .root :: l, none, h => by simp [_root_.Fmt.countItem] at h
  | .f :: l, rt, h => toRoots_some l rt (by simpa [_root_.Fmt.countItem] using h)
  | .word :: l, rt, h => toRoots_some l rt (by simpa [_root_.Fmt.countItem] using h)
  | .e :: l, rt, h => toRoots_some l rt (by simpa [_root_.Fmt.countItem] using h)
  | .answer :: l, rt, h => toRoots_some l rt (by simpa [_root_.Fmt.countItem] using h)

theorem rootsFit_of : ∀ (ds : List RD) (rs : List _root_.Fmt.Round), FitL ds rs → RootsFit ds
  | [], _, _, _, hd, _, _ => by cases hd
  | _ :: _, [], hf, _, _, _, _ => hf.elim
  | d :: ds, r :: rs, hf, d', hd, rt, hrt => by
      obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := hf
      rcases List.mem_cons.1 hd with rfl | hd
      · refine toRoots_some _ rt ?_
        rw [h3, h5, hrt]
        by_cases ht : d'.tree.isSome = true
        · have := h4.1 ht
          rw [if_pos ht]
          omega
        · have : r.entry.roots = 0 := by
            by_contra hne
            exact ht (h4.2 hne)
          rw [if_neg ht, this]
      · exact rootsFit_of ds rs h7 d' hd rt hrt

theorem fitL_length :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round), FitL ds rs → ds.length = rs.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ds, _ :: rs, h => by
      rw [List.length_cons, List.length_cons, fitL_length ds rs h.2.2.2.2.2.2]

/-- If `Fmt.roundsOk` holds of a list of rounds, every round of it passes the round's test (`r.ok`),
at some state. -/
theorem roundsOk_mem (P : _root_.Fmt.Plan) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List _root_.Fmt.Round) (after : Bool) (sent : ℕ),
      _root_.Fmt.roundsOk P nr ft after sent rs = true →
      ∀ r ∈ rs, ∃ after' sent', r.ok P nr ft after' sent' = true
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, r', hr => by
      simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨after, sent, h.1⟩
      · exact roundsOk_mem P nr ft rs _ _ h.2 r' hr

theorem round_facts (P : _root_.Fmt.Plan) (nr : Bool) (ft : ℕ) (after : Bool) (sent : ℕ)
    (r : _root_.Fmt.Round) (h : r.ok P nr ft after sent = true) :
    r.entry.work ≤ 64 ∧ ∀ x ∈ r.opens, x.1.a ≤ 63 := by
  simp only [_root_.Fmt.Round.ok, Bool.and_eq_true, and_assoc, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, -, -, -, hw, -, -, -, -, -, -, -, hl, -, -, -, ho⟩ := h
  exact ⟨hw, fun x hx => by have := (ho x hx).1; omega⟩

/-- The trees' numbers go up one by one, if the n-th tree has the number ft + n. -/
theorem numbered_of :
    ∀ (ds : List RD) (ft : ℕ), (∀ n sh, treeSh ds n = some sh → sh.tree = ft + n) → Numbered ft ds
  | [], _, _ => trivial
  | d :: ds, ft, h => by
      show (match d.tree with
        | none => Numbered ft ds
        | some sh => sh.tree = ft ∧ Numbered (ft + 1) ds)
      cases ht : d.tree with
      | none =>
        refine numbered_of ds ft fun n sh hs => h n sh ?_
        simp only [treeSh, ht]
        exact hs
      | some s =>
        refine ⟨by have := h 0 s (by simp [treeSh, ht]); omega,
          numbered_of ds (ft + 1) fun n sh hs => ?_⟩
        have := h (n + 1) sh (by simp [treeSh, ht]; exact hs)
        omega

theorem treeSh_of_mem :
    ∀ (ds : List RD) (d : RD), d ∈ ds → ∀ sh, d.tree = some sh → ∃ n, treeSh ds n = some sh
  | [], _, hd, _, _ => by cases hd
  | d0 :: ds, d, hd, sh, ht => by
      rcases List.mem_cons.1 hd with rfl | hd
      · exact ⟨0, by simp [treeSh, ht]⟩
      · obtain ⟨n, hn⟩ := treeSh_of_mem ds d hd sh ht
        cases h0 : d0.tree with
        | none => exact ⟨n, by simp only [treeSh, h0]; exact hn⟩
        | some s => exact ⟨n + 1, by simp [treeSh, h0]; exact hn⟩

/-- The n-th tree of a description within the construction's limits (`hok`). -/
theorem own_shape (S : _root_.Fmt.Spec) (hok : ok S = true) (n : ℕ)
    (sh : _root_.Fmt.Shape) (h : treeSh (rds S) n = some sh) :
    n < nRoots S ∧
    sh.tree = S.firstTree + n ∧
    sh.a ≤ 63 ∧
    ((∃ r ∈ S.rounds, ∃ x ∈ r.opens, x.1 = sh) ∨
      (shapeOfOwn S n = none ∧ sh = bareShape S.firstTree n)) := by
  have t := tab_limits S hok
  rw [tab_tree S t n] at h
  by_cases hn : n < nRoots S
  · rw [if_pos hn] at h
    rcases hs : shapeOfOwn S n with _ | s
    · rw [hs] at h
      obtain rfl : bareShape S.firstTree n = sh := Option.some.inj h
      exact ⟨hn, rfl, Nat.zero_le _, Or.inr ⟨rfl, rfl⟩⟩
    rw [hs] at h
    obtain rfl : s = sh := Option.some.inj h
    unfold shapeOfOwn at hs
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hs
    have hm : x ∈ allOpens S := List.mem_of_find?_eq_some hx
    have hp : (ownNo x == some n) = true :=
      List.find?_some (p := fun o : _root_.Fmt.Shape × _root_.Fmt.Src => ownNo o == some n) hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hm
    obtain ⟨n', g⟩ := tab_good S t r hr x hxr
    have e1 : x.2 = _root_.Fmt.Src.own n := (tab_ownNo x n).1 (beq_iff_eq.1 hp)
    have e2 : n' = n := by
      have := g.src.symm.trans e1
      injection this
    obtain ⟨af, se, hro⟩ := roundsOk_mem _ _ _ S.rounds _ _ t.rok r hr
    exact ⟨hn, e2 ▸ g.tree, (round_facts _ _ _ _ _ r hro).2 x hxr, Or.inl ⟨r, hr, x, hxr, rfl⟩⟩
  · rw [if_neg hn] at h
    cases h

/-- The format's own conditions (`S.ok`), out of the construction's limits (`ok S`). -/
theorem specOk_of (S : _root_.Fmt.Spec) (hok : ok S = true) : S.ok = true := by
  simp only [ok, Bool.and_eq_true] at hok
  exact hok.1.1.1.1

/-- What is asked of a description (`FitsS S K`) holds within the construction's limits (`hok`),
under four bounds on numbers (`hK`, `hst`, `hlen`, `hft`). -/
theorem fitsS_of (S : _root_.Fmt.Spec) (K : ℕ) (hok : ok S = true) (hK : K + 1 < 2 ^ 48)
    (hst : S.statement.size < 2 ^ 64) (hlen : S.rounds.length < 2 ^ 64)
    (hft : S.firstTree + nRoots S ≤ 2 ^ 48) : FitsS S K where
  k48 := hK
  work := fun r hr => by
    obtain ⟨af, se, hro⟩ := roundsOk_mem _ _ _ S.rounds _ _ (tab_limits S hok).rok r hr
    have := (round_facts _ _ _ _ _ r hro).1
    omega
  stm := hst
  roots := rootsFit_of (rds S) S.rounds (fit_rds S hok)
  len := by rw [fitL_length (rds S) S.rounds (fit_rds S hok)]; exact hlen
  num := numbered_of (rds S) S.firstTree fun n sh hs => (own_shape S hok n sh hs).2.1
  small := fun d hd sh ht => by
    obtain ⟨n, hn⟩ := treeSh_of_mem (rds S) d hd sh ht
    obtain ⟨h1, h2, h3, hopen⟩ := own_shape S hok n sh hn
    have hc := _root_.Fmt.ok_count (specOk_of S hok)
    have hs := _root_.Fmt.ok_small (specOk_of S hok)
    simp only [_root_.Fmt.Spec.small, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    have hn' : n < (S.rounds.map (·.entry.roots)).sum := h1
    rcases hopen with ⟨r, hr, x, hx, e⟩ | ⟨-, e⟩
    · exact ⟨⟨by omega, e ▸ (hs.1.2 r hr x hx).2⟩, h3⟩
    · exact ⟨⟨by omega, by rw [e]; exact (by decide : (1 : ℕ) < 2 ^ 24)⟩, h3⟩
  salt := by
    have := _root_.Fmt.ok_salt (specOk_of S hok)
    simp only [_root_.Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq] at this
    omega

/-- Under `hok`, `h` and the four bounds `hK`, `hst`, `hlen`, `hft`: the run over the single oracle
through the encoding is the run at the typed oracle functions, including who decided, on every file.
-/
theorem one_is_typed (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool) (file : ByteArray)
    (hok : ok S = true) (h : OKQ S = true) (hK : K + 1 < 2 ^ 48) (hst : S.statement.size < 2 ^ 64)
    (hlen : S.rounds.length < 2 ^ 64) (hft : S.firstTree + nRoots S ≤ 2 ^ 48) :
    run1C S C K chal dec file = runLaxC S C K chal dec file := by
  refine one_file S C K chal dec file h ?_
  unfold askedFile
  rw [dif_pos h]
  cases e : parseLaxFP (PSof C (rds S) dec) S (TYS S C dec) file with
  | none => rfl
  | some x =>
    match x, e with
    | ([], _), _ => rfl
    | ([cm], π), e =>
      have e' := ((laxFast_parse _ S _ file).1).symm.trans e
      obtain ⟨h1, h2⟩ := parse_facts S C dec hok file cm π e'
      show askedQK S C K chal dec h cm π = true
      rw [askedQK_eq]
      exact asked_of S C K chal dec h (fitsS_of S K hok hK hst hlen hft) cm π h1 h2
    | (_ :: _ :: _, _), _ => rfl

/-- The four bounds on numbers, as a test that can be run at a closed description. -/
def fourBounds (S : _root_.Fmt.Spec) (K : ℕ) : Bool :=
  decide (K + 1 < 2 ^ 48) && decide (S.statement.size < 2 ^ 64) &&
    decide (S.rounds.length < 2 ^ 64) && decide (S.firstTree + nRoots S ≤ 2 ^ 48)

theorem one_is_typedB (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool) (file : ByteArray)
    (hok : ok S = true) (h : OKQ S = true) (hb : fourBounds S K = true) :
    run1C S C K chal dec file = runLaxC S C K chal dec file := by
  simp only [fourBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact one_is_typed S C K chal dec file hok h hb.1.1.1 hb.1.1.2 hb.1.2 hb.2

/-- At the choice `ckP` (challenges as hash blocks), under `hok`, `h` and `hb`: the fast run
function over the single oracle (`run1PF`) is the run function at typed oracle functions
(`runLaxSP`). -/
theorem one_pull (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) (hok : ok S = true)
    (h : OKQ S = true) (hb : fourBounds S (kOf S) = true) :
    run1PF S dec file = runLaxSP S dec file :=
  (run1pf_eq S dec file).trans (one_is_typedB S _ _ _ dec file hok h hb)

/-- The run of Run/PageQRun.lean (`run1`) is the run with the choice of challenge types as a
parameter (`run1C`), at `ck` (challenges as sampled values). -/
theorem run1_atCk (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) :
    run1 S dec file = run1C S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file := by
  unfold run1 run1C
  generalize parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
      (TYS S (ck S.plan.field) dec) file = x
  unfold run1On run1COn
  by_cases hk : ok S = true
  · rw [if_pos hk, if_pos hk]
    by_cases h : OKQ S = true
    · rw [dif_pos h, dif_pos h]
      match x with
      | none => rfl
      | some ([], _) => rfl
      | some ([cm], π) =>
        simp only
        rw [v1_is S dec h cm π]
      | some (_ :: _ :: _, _) => rfl
    · rw [dif_neg h, dif_neg h]
  · rw [if_neg hk, if_neg hk]

/-- At the choice `ck` (challenges as sampled values), under `hok`, `h` and `hb`: `run1K` is
`runLaxS`. -/
theorem one_ck (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) (hok : ok S = true)
    (h : OKQ S = true) (hb : fourBounds S (kOf S) = true) :
    run1K S dec file = runLaxS S dec file := by
  rw [run1K_eq, run1_atCk]
  exact one_is_typedB S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file hok h hb

end Run.PQ

-- the three tests hold at the programs' own parameters, tiny and full
open Run.PQ _root_.Fmt.M1 in
#guard ok Theirs.specTiny && OKQ Theirs.specTiny && fourBounds Theirs.specTiny (kOf Theirs.specTiny)
open Run.PQ _root_.Fmt.M1 in
#guard ok Theirs.specFull && OKQ Theirs.specFull && fourBounds Theirs.specFull (kOf Theirs.specFull)
