-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageXAsked.lean: on an argument string (the proof in typed form, `OneProtocolProof`) of the form that the
typing makes, the compiled verifier of a chain with stored tables asks only queries that the
encoding of Run/PageX.lean writes in the format; so its run at `famXPd` (Run/PageXFit.lean) is its
run at the family that the encoding reads out of a function on bit strings.

Theorems. Run/OneIsTyped*.lean has this for plain chains, at the format's own hash, through a
general tool: the evaluable form of the compiled verifier gives one verdict at two families that
agree where two tests on queries hold (at round 0: in the chain value alone; the first round's
wiring must not look at its blocks, `FrontBlind`), if every query that it forms passes them
(Run/ThinAsked.lean: `askedP`, `verifyP_asked`). Here the tests are `fitsCX`
(Run/CodingAgreeX.lean) at the data `pageXPd`, the protocol is `skeletonOverBothExternalStrings` at the tag "link", under two
roots, and the leaves of the two stored tables are among the queries. pd (256 bits) is the argument
of Run/PageX.lean and Run/PageXFit.lean: it stands in the first query's string and in `famXPd`.

Main names:
  `StoredFits D op`: an opening of a stored table: its salt begins with the configuration's digest,
    its column has fewer than 2^24 words, and 2^a + its position is below 2^64.
  `TypedOK D dec cm cm' π`: what is asked of an argument string: a first salt of 256 bits; nonces
    below 2^64; every opening of a stored table has `StoredFits`; the statement of the two roots has
    fewer than 2^64 bytes.
  `askP_allX`: every chain query that the verifier forms passes the test, at every family.
  `own_fitsX`, `stored_fitsX`: leaf queries of the two kinds pass the test.
  `askedX`: `FitsS D.base D.K` (Run/OneIsTypedTop.lean) and `TypedOK` imply `askedP .. = true`, at
    every family.
  `verifyP_readX`, `verifyBS_readX`: under these two, for every g : Fam (rom 256): the verifier's
    run on π at `famXPd D dec (digToBytes pd) (oB (g ())) (D.K + 1)` is its run at
    `readBlocks (theImplX (pageXPd ..)) g`.

Limits: nothing on soundness, and no probability. Nothing on BLAKE2b or on any other hash: pd is any
256 bits, an argument of every theorem here on a test or a family, and nothing ties it to the
parameter bytes. For an argument string without `TypedOK` nothing is said: its four fields (a first
salt of 256 bits; nonces below 2^64; `StoredFits` at every opening of a stored table; a statement of
fewer than 2^64 bytes) are what a maker of argument strings other than `toBPrfX` behind a reader has
to meet for the equations of this file. Outside them the two families part in two ways. (1) The
verifier tests only the length of a leaf's salt (`strictExt`, Compile/Bcs.lean), so a string can
make it ask a leaf of a stored table whose typed salt does not begin with the configuration's
digest: `famXPd` has no call for it and answers zeros, whatever the symbol, and the encoding writes
it behind an escape. (2) At a nonce that is not below 2^64, and at a stored symbol whose width or
position is beyond `StoredFits`, `famXPd` still has a call; its words are spelled by `Fmt.u64n`,
which takes a number modulo 2^64, so different typed queries can have one call; the encoding writes
such a query behind an escape. Whether the verdicts at the two families then differ is not examined,
and whether the verifier bounds these numbers elsewhere is not traced. That what the typing makes of
a chain that was read has `TypedOK` is not shown in this file (Run/PageXRead.lean
[not in this library], Run/PageXLax.lean [not in this library], Run/PageXReadAt.lean
[not in this library]).

Terms: lean/GLOSSARY.md.

-/
import Run.PageXFit
import Run.OneIsTypedTop
import Run.ThinTie

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

variable (D : XD) (dec : View → Bool) (pd : Dig 256) (hcfg : D.base.cfg.size = 32)
  (V : StmInv D)

/-- The test on a chain query: `fitsCX` at the data of the description and pd. -/
abbrev PqX : FbIn 256 (D.L dec) .link → Bool := fitsCX (pageXPd dec pd (D.K + 1) hcfg V) (.fb .link)

/-- The test on a leaf query: `fitsCX` at the data of the description and pd. -/
abbrev PlX : LeafIn (D.L dec) → Bool := fitsCX (pageXPd dec pd (D.K + 1) hcfg V) .leaf

/-- How the verifier carries a plain part over to the interface. -/
abbrev embX : PlainPart (Twin.up (SOf D.C D.ds)) (Twin.allLo (SOf D.C D.ds)) → PBX D dec :=
  embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())

/-- The wiring of the protocol: `wqX` (Run/PlanQX.lean) at the description. -/
abbrev wX : ProtocolQueryLayout 256 (D.K + 1) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up :=
  wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec

/-! ## Chain queries -/

/-- A chain query of a round behind the first passes the test, if its chain value has 256 bits,
its plain part belongs to the rounds behind the first (`.inr pl`) and fits round i there (`okL`),
and the numbers are within the words' bounds. -/
theorem later_fitsX (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256)
    (i : ℕ) (ρ : Bits) (rt : Option (Dig 256)) (pl : PBL D.C D.ds) (hρ : ρ.length = 256)
    (hi : i + 1 < 2 ^ 64) (hk : okL D.C D.ds i rt pl = true) :
    PqX D dec pd hcfg V ⟨i + 1, .f2 none ρ, rt, .inr pl⟩ = true := by
  show fitsCX (pageXPd dec pd (D.K + 1) hcfg V) (.fb .link) _ = true
  rw [fitsCX_fb, if_neg (Nat.succ_ne_zero i), List.all_eq_true]
  intro j _
  refine fitsQ_put D.base D.C dec (D.K + 1) ⟨i + 1, .f2 none ρ, rt, .inr pl⟩ ?_ j
  unfold fitsQ
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hρ, hi⟩, kindQ_lt D.base D.C dec _⟩, workQ_lt D.base D.C dec hw _⟩, hK⟩, hk⟩

/-- One step of the test on the chain (`askP`, Run/ThinAsked.lean), at a local round behind the
first, with no statement. -/
theorem askP_loX {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)
    (g : Fam (spec lam K (Lf ()))) (t : Tag) (Pq : FbIn lam (Lf ()) t → Bool) (cms : List (Dig lam))
    (salt : Bits) (r : RS) (Ss : List RS) (A : RoundSplits (up Ss))
    (w : WireRB lam K r.up r.lo) (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) →
      PlainPart (Compile.Batch.shapeOf (Lf ()) t) (Compile.Batch.annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) :
    askP Lf g id none t Pq cms (none : Option X) salt (r :: Ss) (r.lo, A) (w, W) embP i
      (.loc v) rts (pl, pls) =
      match takeRt w.hasJ rts with
      | some (rt, rts') =>
        Pq ⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ &&
          askP Lf g id none t Pq cms (none : Option X) salt Ss A W
            (fun z => embP (.inr z)) (i + 1)
            (.loc (List.ofFn
                (g (OracleName.fb t)
                  (⟨i, .f2 none v, rt,
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
            rts' pls
      | none => true := rfl

/-- The chain queries of the rounds behind the first pass the test, at every family. By
induction on a suffix of the list of rounds, as in the proof for plain chains
(Run/OneIsTypedChain.lean). -/
theorem askP_tailX (g : Fam (spec 256 (D.K + 1) (D.L dec))) (cms : List (Dig 256)) (salt : Bits)
    (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256) :
    ∀ (ds : List RD) (n : ℕ) (embP : PlainPart (uL D.C ds) (allLo (SL D.C ds)) → PBX D dec) (ρ : Bits)
        (rts : List (Dig 256)) (pls : Plains (uL D.C ds)),
      ρ.length = 256 →
      (∀ z, ∃ pl : PBL D.C D.ds,
        embP z = .inr pl ∧
          ∀ k rt, okL D.C D.ds (n + k) rt pl = okL D.C ds k rt (embPL D.C ds z)) →
      RootsFit ds → noncesOK D.C ds pls → n + ds.length < 2 ^ 64 →
      askP (lam := 256) (K := D.K + 1) (fun _ => D.L dec) g id none .link (PqX D dec pd hcfg V)
          cms (none : Option Unit) salt (SL D.C ds) (allLo (SL D.C ds))
          (wiresSL D.C D.K (chalP D.base.plan.field D.K) ds) embP (n + 1) (.loc ρ) rts pls = true
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | d :: ds, n, embP, ρ, rts, (pl, pls), hρ, hemb, hr, hn, hlen => by
    refine (askP_loX (fun _ => D.L dec) g .link (PqX D dec pd hcfg V) cms salt
      (roundS D.C d) (SL D.C ds) (allLo (SL D.C ds))
      (wireS D.C D.K (chalP D.base.plan.field D.K) d)
      (wiresSL D.C D.K (chalP D.base.plan.field D.K) ds) embP (n + 1) ρ rts pl pls).trans ?_
    cases ht : takeRt (wireS D.C D.K (chalP D.base.plan.field D.K) d).hasJ rts with
    | none => rfl
    | some x =>
      obtain ⟨rt, rts'⟩ := x
      obtain ⟨pl', he, hk⟩ := hemb (.inl (.inr pl))
      have hlen' : n + (ds.length + 1) < 2 ^ 64 := hlen
      have hfit : PqX D dec pd hcfg V
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (D.L dec) .link) = true := by
        rw [he]
        refine later_fitsX D dec pd hcfg V hK hw n ρ rt pl' hρ (by omega) ?_
        have := hk 0 rt
        rw [Nat.add_zero] at this
        rw [this]
        exact okRound_of d.entry.work d.items rt pl
          (hr d List.mem_cons_self rt (takeRt_isSome _ _ _ _ ht)) hn.1
      show (PqX D dec pd hcfg V
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (D.L dec) .link) &&
          _) = true
      rw [hfit, Bool.true_and]
      refine askP_tailX g cms salt hK hw ds (n + 1) (fun z => embP (.inr z)) _ rts' pls
        List.length_ofFn ?_ (fun d' hd' => hr d' (List.mem_cons_of_mem _ hd')) hn.2 (by omega)
      intro z
      obtain ⟨pl2, he2, hk2⟩ := hemb (.inr z)
      refine ⟨pl2, he2, fun k rt => ?_⟩
      have := hk2 (k + 1) rt
      rw [show n + (k + 1) = n + 1 + k by omega] at this
      exact this

/-- The first chain query passes the test: two roots, a salt of 256 bits, a statement of fewer
than 2^64 bytes. -/
theorem first_fitsX (cm cm' : Dig 256) (salt : Bits) (hs : salt.length = 256)
    (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64) :
    PqX D dec pd hcfg V
        (⟨0, .f1 [cm, cm'] none salt, none, embX D dec (.inl (.inr ()))⟩ :
          FbIn 256 (D.L dec) .link) = true := by
  show fitsCX (pageXPd dec pd (D.K + 1) hcfg V) (.fb .link) _ = true
  rw [fitsCX_fb, if_pos rfl]
  show ((first0X V).put (pd, some (cm, cm'), salt)).isSome = true
  unfold first0X
  rw [pFirst0_put D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V) pd
    (some (cm, cm')) salt _ rfl hst (Or.inr hs)]
  rfl

/-- Every chain query that the verifier forms passes the test, at every family. -/
theorem askP_allX (g : Fam (spec 256 (D.K + 1) (D.L dec))) (cm cm' : Dig 256) (salt : Bits)
    (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256)
    (hs : salt.length = 256) (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64)
    (hr : RootsFit D.ds) (hlen : D.ds.length < 2 ^ 64)
    (rts : List (Dig 256)) (pls : Plains (uL D.C D.ds)) (hn : noncesOK D.C D.ds pls) :
    askP (lam := 256) (K := D.K + 1) (fun _ => D.L dec) g id none .link (PqX D dec pd hcfg V)
        [cm, cm'] (none : Option Unit) salt (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh (embX D dec) 0 .first rts ((), pls) =
      true := by
  show (PqX D dec pd hcfg V
        (⟨0, .f1 [cm, cm'] none salt, none, embX D dec (.inl (.inr ()))⟩ :
          FbIn 256 (D.L dec) .link) && _) = true
  rw [first_fitsX D dec pd hcfg V cm cm' salt hs hst, Bool.true_and]
  refine askP_tailX D dec pd hcfg V g [cm, cm'] salt hK hw D.ds 0
    (fun z => embX D dec (.inr z)) _ rts pls List.length_ofFn ?_ hr hn (by omega)
  intro z
  exact ⟨embPL D.C D.ds z, rfl, fun k rt => by rw [Nat.zero_add]⟩

/-! ## Leaf queries -/

/-- A leaf query on a symbol of the protocol, with a salt of the format's length, passes the
test, if the trees are numbered one after the other and are small, and the plan's salt has fewer
than 2,048 bytes. -/
theorem own_fitsX (ft : ℕ) (hN : Numbered ft D.ds) (hS : SmallTrees D.ds)
    (hsalt : D.base.plan.salt / 8 < 2 ^ 8) (p : OPos (Twin.up (SOf D.C D.ds)))
    (a : OSym (Twin.up (SOf D.C D.ds)) p) (salt : Bits)
    (hl : salt.length = 256 + 8 * D.base.plan.salt) :
    PlX D dec pd hcfg V (⟨some (.inr ⟨Tag.link, ⟨p, a⟩⟩), salt⟩ : LeafIn (D.L dec)) = true := by
  have h1 : ((leafPX D dec).put ⟨p, a⟩).isSome = true := by
    cases p with
    | inl e => exact e.elim
    | inr q =>
      show (((leafCL D.C D.base.plan.salt D.ds).put ⟨q, a⟩).filter fun s =>
          ((PCode.empty (Σ p : Empty, OSym (Twin.up (SOf D.C D.ds)) (.inl p))).parse
            s).isNone).isSome = true
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1
        (leafCL_some D.C D.base.plan.salt hsalt D.ds ft hN hS ⟨q, a⟩)
      rw [hm]
      rfl
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h1
  have h2 : (pLeaf (8 * D.base.plan.salt) (leafPX D dec)).put
      (⟨some (.inr ⟨Tag.link, ⟨p, a⟩⟩), salt⟩ : LeafIn (D.L dec)) =
      some (pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) := by
    show ((if salt.length = 256 + 8 * D.base.plan.salt then
      ((leafPX D dec).put ⟨p, a⟩).map fun m =>
        pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)) else none) : Option (List Bool)) = _
    rw [if_pos hl, hm]
    rfl
  have h3 : (pLeaf2 (pageXPd dec pd (D.K + 1) hcfg V)).put
      (⟨some (.inr ⟨Tag.link, ⟨p, a⟩⟩), salt⟩ : LeafIn (D.L dec)) = some _ :=
    PCode.join_left _ _ _ _ h2
  show ((pLeaf2 (pageXPd dec pd (D.K + 1) hcfg V)).put _).isSome = true
  rw [h3]
  rfl

/-- What is asked of an opening of a stored table: the first 256 bits of its salt are the
configuration's digest; its column has fewer than 2^24 words; 2^a + its position is below 2^64. -/
def StoredFits (op : Opening 256 SgX) : Prop :=
  bitsToBytes (op.salt.take 256) = D.base.cfg ∧ op.sym.2.length < 2 ^ 24 ∧
    2 ^ D.a + op.sym.1 < 2 ^ 64

/-- A leaf query on a symbol of a stored table passes the test, if the opening has `StoredFits`
and a salt of the format's length, and the plan's salt has fewer than 2,048 bytes. -/
theorem stored_fitsX (hsalt : D.base.plan.salt / 8 < 2 ^ 8) (op : Opening 256 SgX)
    (h : StoredFits D op) (hl : op.salt.length = 256 + 8 * D.base.plan.salt) :
    PlX D dec pd hcfg V (⟨some (.inl op.sym), op.salt⟩ : LeafIn (D.L dec)) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  have hm := pStored_some D.a D.base.plan.salt op.sym
    ⟨h2, by unfold _root_.Fmt.leafPlace; omega, h3⟩
  have hp := pLeafS_some (L := D.L dec) D.base.cfg (8 * D.base.plan.salt)
    (pStored D.a D.base.plan.salt) op.sym op.salt _
    (by
      show (bitsToBytes (op.salt.take 256) == D.base.cfg) = true
      rw [h1]
      exact bytes_beq_self _) hl hm
  have h4 : (pLeaf2 (pageXPd dec pd (D.K + 1) hcfg V)).put
      (⟨some (.inl op.sym), op.salt⟩ : LeafIn (D.L dec)) = some _ :=
    PCode.join_right _ _ _ _ hp
  show ((pLeaf2 (pageXPd dec pd (D.K + 1) hcfg V)).put _).isSome = true
  rw [h4]
  rfl

/-- Every check that the verifier collects over external positions holds the symbol and the salt of
an opening that the argument string has at one of these positions. -/
theorem extWP_inp {I X : Type} {lam : ℕ} (Lf : Unit → BatchProtocol I X) {E : ExtSpec} (we : WireE E)
    (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam)) (isRead : E.Pos → Bool)
    (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (ℕ × Check lam (Lf ()))),
      extWP Lf we emb cms isRead f ps = some cs →
      ∀ c ∈ cs, ∃ p ∈ ps, ∃ op, f p = some op ∧ c.2.inp = ⟨emb op.sym, op.salt⟩
  | [], cs, h, c, hc => by
    rw [← Option.some.inj h] at hc
    cases hc
  | p :: ps, cs, h, c, hc => by
    have ih : ∀ cs', extWP Lf we emb cms isRead f ps = some cs' → ∀ c' ∈ cs',
        ∃ p' ∈ p :: ps, ∃ op, f p' = some op ∧ c'.2.inp = ⟨emb op.sym, op.salt⟩ := by
      intro cs' h' c' hc'
      obtain ⟨p', hp', r⟩ := extWP_inp Lf we emb cms isRead f ps cs' h' c' hc'
      exact ⟨p', List.mem_cons_of_mem _ hp', r⟩
    simp only [extWP] at h
    split at h
    · split at h
      · rename_i op cs' e1 e2
        rw [← Option.some.inj h] at hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨p, List.mem_cons_self, op, e1, rfl⟩
        · exact ih cs' e2 c hc
      · cases h
    · exact ih cs h c hc

/-! ## The test on an argument string -/

/-- What is asked of an argument string, under the two roots cm and cm'. -/
structure TypedOK (cm cm' : Dig 256) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) : Prop where
  /-- the first salt has 256 bits -/
  salt   : π.salt.length = 256
  /-- the nonces are below 2^64 -/
  nonces : noncesOK D.C D.ds π.plains.2
  /-- every opening of a stored table fits -/
  ext    : ∀ p op, π.ext p = some op → StoredFits D op
  /-- the statement of the two roots can be spelled -/
  stm    : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64

/-- On such a string every query that the verifier forms passes the tests, at every family g. In the
terms of Run/ThinAsked.lean `askedP .. = true`: every chain query passes `PqX`; the chain never
joins, so no oracle of a request tree is asked; where the strict format holds, every leaf query
passes `PlX`. Where it fails, the verifier refuses before it asks a leaf. A vertex's query is two
digests and has no test. Which queries are formed depends on g; that each passes does not: a chain
value has 256 bits at every g, and all else in a query comes from π. Asked: `FitsS D.base D.K` and
`TypedOK`. -/
theorem askedX (F : FitsS D.base D.K) (g : Fam (spec 256 (D.K + 1) (D.L dec))) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) (T : TypedOK D dec cm cm' π) :
    askedP (lam := 256) (K := D.K + 1) (fun _ => D.L dec) g id none
      (256 + 8 * D.base.plan.salt) 256 .link (PqX D dec pd hcfg V) (PlX D dec pd hcfg V)
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π = true := by
  unfold askedP
  rw [Bool.and_eq_true]
  refine ⟨askP_allX D dec pd hcfg V g cm cm' π.salt F.k48 F.work T.salt T.stm F.roots F.len π.roots
    π.plains.2 T.nonces, ?_⟩
  cases hc : chainP (lam := 256) (K := D.K + 1) (fun _ => D.L dec) g id none .link [cm, cm']
      (none : Option Unit) π.salt π.rtreq (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh (embX D dec) 0 .first π.roots π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    show (!strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
          (wX D dec) 0 () π ρ rts ph || _) = true
    by_cases hst : strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
        (wX D dec) 0 () π ρ rts ph = true
    · rw [hst, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have := chainP_local (fun _ => D.L dec) g id none .link [cm, cm']
          (none : Option Unit) π.salt π.rtreq (SOf D.C D.ds) (wX D dec).sh
          (embX D dec) 0 .first π.roots π.plains (ρ, rts, ph) rfl hc
        rw [show ph.slotVal = none from this]
        rfl
      · cases hf : forestsOfP (fun _ => D.L dec) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
            (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
            (fun s => some (.inl s)) [cm, cm'] () π ρ rts with
        | none => rfl
        | some Fs =>
          show ((flatP (fun _ => D.L dec) Fs).all fun c => PlX D dec pd hcfg V c.inp) = true
          rw [List.all_eq_true]
          intro c hcm
          simp only [strictP, Bool.and_eq_true] at hst
          have h3 := hst.1.1.1.2
          have h4 := hst.1.1.2
          simp only [forestsOfP] at hf
          split at hf
          · rename_i a b e1 e2
            rw [← Option.some.inj hf, flatP_append] at hcm
            rcases List.mem_append.1 hcm with hcm | hcm
            · obtain ⟨p, s, salt, i1, i2⟩ := forestsP_inp (fun _ => D.L dec)
                (256 + 8 * D.base.plan.salt) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
                (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh _ rts _ π.opens a e1 h3 c hcm
              rw [i1]
              exact own_fitsX D dec pd hcfg V D.base.firstTree F.num F.small F.salt p s salt i2
            · unfold forestExtP at e2
              obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 e2
              obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_flat_split (fun _ => D.L dec) _ _ c hcm)
              obtain ⟨p, hp, op, ho, i1⟩ := extWP_inp (fun _ => D.L dec) _ _ _ _ _ _ cs hcs x hx
              rw [i1]
              have hl : op.salt.length = 256 + 8 * D.base.plan.salt := by
                unfold sExtP strictExt at h4
                have := List.all_eq_true.1 h4 p hp
                rw [ho] at this
                simp only [Bool.and_eq_true, decide_eq_true_eq] at this
                exact this.2
              exact stored_fitsX D dec pd hcfg V F.salt op (T.ext p op ho) hl
          · cases hf
    · rw [Bool.not_eq_true] at hst
      rw [hst]
      rfl

/-! ## The verifier at the two families -/

/-- The evaluable form of the compiled verifier, at `famXPd` and at what the encoding reads out of
g. For a description with `FitsS`, an argument string with `TypedOK`, and every g. An equation
between two runs: of neither is it said that it accepts. Nothing on soundness; no probability. -/
theorem verifyP_readX (F : FitsS D.base D.K) (g : Fam (rom 256)) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) (T : TypedOK D dec cm cm' π) :
    verifyP (fun _ => D.L dec) (famXPd D dec (digToBytes pd) (oB (g ())) (D.K + 1)) id none
        (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embX D dec) (fun _ => none)
        (fun s => some (.inl s)) 0 [cm, cm'] () π =
      verifyP (fun _ => D.L dec) (readBlocks (theImplX (pageXPd dec pd (D.K + 1) hcfg V)) g) id none
        (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embX D dec) (fun _ => none)
        (fun s => some (.inl s)) 0 [cm, cm'] () π := by
  have hw : FrontBlind (lam := 256) (K := D.K + 1) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh :=
    fun _ _ => Subsingleton.elim _ _
  refine verifyP_asked (fun _ => D.L dec) _ _ id none _ 256 .link
    (PqX D dec pd hcfg V) (PlX D dec pd hcfg V) ?_ ?_ ?_ (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wX D dec) hw _ _ _ _ 0 [cm, cm'] () π (askedX D dec pd hcfg V F _ cm cm' π T)
  · intro q hq
    exact ⟨famXPd_last_read dec pd (D.K + 1) (Nat.succ_pos _) hcfg V g q hq,
      famXPd_whole_read dec pd (D.K + 1) (Nat.succ_pos _) hcfg V g q hq⟩
  · intro q hq
    exact famXPd_leaf_read dec pd (D.K + 1) (Nat.succ_pos _) hcfg V g q hq
  · intro a b
    exact famXPd_node_read dec pd (D.K + 1) (Nat.succ_pos _) hcfg V g a b

/-- The run of the compiled verifier, at `famXPd` and at what the encoding reads out of g. The
same for `Compile.Batch.verifyOneProtocol` itself. An equation between two runs: of neither is it said that
it accepts. Nothing on soundness; no probability. -/
theorem verifyBS_readX (F : FitsS D.base D.K) (g : Fam (rom 256)) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) (T : TypedOK D dec cm cm' π) :
    (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (famXPd D dec (digToBytes pd) (oB (g ())) (D.K + 1)) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (readBlocks (theImplX (pageXPd dec pd (D.K + 1) hcfg V)) g) := by
  rw [← thin_verify Unit Unit 256 _ (D.L dec) (famXPd D dec (digToBytes pd) (oB (g ()))
      (D.K + 1)) Unit _ _ 256 .link
      _ _ _ _ (fun _ => none) (fun s => some (.inl s)) 0 _ () π,
    ← thin_verify Unit Unit 256 _ (D.L dec) (readBlocks (theImplX (pageXPd dec pd
        (D.K + 1) hcfg V)) g)
      Unit _ _ 256 .link _ _ _ _ (fun _ => none) (fun s => some (.inl s)) 0 _ () π]
  exact verifyP_readX D dec pd hcfg V F g cm cm' π T

end Run.PQ
