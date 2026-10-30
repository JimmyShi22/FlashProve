-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageXAsked.lean: on an argument string of the form that the typing makes, the
sibling's compiled verifier of a chain with stored tables asks only queries that the encoding of
OnBytes/TypedOracleCompiler/Run/PageXFit.lean writes in the format; so its run at `famXPd` is its run at the family
that the encoding reads out of a function on bit strings.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/PageXAsked.lean (17 declarations, 422 lines), over the sibling's thin verifier
(OnBytes/TypedOracleCompiler/Run/ThinDefs.lean, ThinAsked.lean, ThinAskedMore.lean, ThinTieProofs.lean). The
verifier's two embeddings of bodies are arguments: `embS`, of the chain's own typed symbols, is a
variable; that of stored symbols is `B.embE`.

AS TEXT BUT FOR NAMES AND THE NEW ARGUMENTS; a query's roots are a list (12). `PqX`, `PlX`, `embX`,
`wX`, `later_fitsX`, `first_fitsX`, `askP_allX`, `StoredFits`, `extWP_inp`, `TypedOK`,
`verifyP_readX`, `verifyBS_readX`.
TURNED (5).
 `askP_loX`           the roots of a round are taken by the NUMBER of its trees (`takeRt
                      w.depthJ.length`), where the original takes one or none by a flag.
 `askP_tailX`         that the roots fit the items follows from their number (`takeRt_length`,
                      `RootsFit`).
 `own_fitsX`          by `OwnFits`, where the original has the library's `leafCL_some` under the
                      trees' numbering and size.
 `stored_fitsX`       through `pLeafC_stored` and `storedIn_pageXPd`.
 `askedX`             the embeddings are `embS` and `B.embE`; `OwnFits` is asked beside `FitsS` and
                      `TypedOK`.
NEW (8).
 `OwnFits B D Lf embS`   what is asked of the bodies of the chain's own symbols: the code of bodies
                      WRITES each, and none is a stored symbol. The converse of `LeafD.own`.
 `takeRt_length`      what the sibling's `takeRt` takes has the length that was asked.
 `noncesOK`, `okRound_of`, `kindQ_lt`, `workQ_lt`   the library's text (Run/OneIsTypedChain.lean,
                      Run/OneIsTypedTop.lean), which is not said over the sibling.
 `RootsFit`, `FitsS`  the library's notions, turned: as many roots as the round has trees; without
                      the clauses on the statement in the description and on the own trees'
                      numbering and size.
NO COUNTERPART: none.

WHAT IS NOT SAID. That any embedding meets `OwnFits`, or any description `FitsS`. That `B.own (embS
p a)` is the library's spelling `leafSL` of the symbol: it is not needed here; a tie with what a
reader has read will need it. That what the typing makes of a chain that was read has `TypedOK`
(OnBytes/TypedOracleCompiler/Run/PageXRead.lean). For an argument string without `TypedOK` nothing is said. pd is
any 256 bits. Equations between two runs: of neither is it said that it accepts. Nothing on
soundness; no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.TypedOracleCompiler.Run.PageQFits
import OnBytes.TypedOracleCompiler.Run.ThinAskedMore
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
import Run.OneIsTypedChain

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Item)

/-! ## What the library's files on typed strings have, over the sibling's rounds' data -/

/-- The nonces are below 2^64. The library's text. -/
def noncesOK (C : CK) : (ds : List RD) → Plains (uL C ds) → Prop
  | [], _ => True
  | d :: ds, (pl, pls) => nonceOK d.entry.work pl ∧ noncesOK C ds pls

/-- TWO: as many roots as the round has trees fit the round's items. -/
def RootsFit (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ rt : List (Dig 256), rt.length = d.trees.length → (toRoots d.items rt).isSome = true

/-- TWO: what `takeRt` takes has the length that was asked. -/
theorem takeRt_length {lam : ℕ} (n : ℕ) (rts rt rts' : List (Dig lam))
    (h : takeRt n rts = some (rt, rts')) : rt.length = n := by
  unfold takeRt at h
  split at h
  · rename_i hc
    rw [← (Prod.mk.inj (Option.some.inj h)).1, List.length_take]
    omega
  · cases h

/-- Roots that fit and a nonce below 2^64 pass the round's test. The library's text. -/
theorem okRound_of (w : ℕ) (l : List Item) (rt : List (Dig 256)) (p : GPlain ℕ w (PlainOf l))
    (h1 : (toRoots l rt).isSome = true) (h2 : nonceOK w p) : okRound w l rt p = true := by
  cases w with
  | zero => exact h1
  | succ n =>
    show ((toRoots l rt).isSome && decide ((p : PlainOf l × ℕ).2 < 2 ^ 64)) = true
    rw [h1, Bool.true_and, decide_eq_true_iff]
    exact h2

/-- A round's kind is below 256. The library's text. -/
theorem kindQ_lt (Bd : Type) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (i : ℕ) :
    (chainQ Bd S C dec).kind i < 256 := by
  show (if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7) < 256
  split
  · omega
  · cases S.rounds[i - 1]? with
    | none => show 7 < 256; omega
    | some r =>
      show r.kind.num < 256
      cases r.kind <;> simp [_root_.Fmt.Kind.num]

/-- A round's work is below 256, if every round's is. The library's text. -/
theorem workQ_lt (Bd : Type) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)
    (hw : ∀ r ∈ S.rounds, r.entry.work < 256) (i : ℕ) : (chainQ Bd S C dec).work i < 256 := by
  show (if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0) < 256
  split
  · omega
  · cases hr : S.rounds[i - 1]? with
    | none => show 0 < 256; omega
    | some r => exact hw r (List.mem_of_getElem? hr)

/-- What is asked of a description and the number of blocks. The library's `FitsS` without its
clauses on the statement in the description (not read here) and on the numbering and the size of the
chain's own trees: there they serve the typed code of own leaves; here: `OwnFits`'s matter. -/
structure FitsS (S : _root_.Fmt.Spec) (K : ℕ) : Prop where
  /-- the number of blocks fits its word -/
  k48   : K + 1 < 2 ^ 48
  /-- every round's work fits its byte -/
  work  : ∀ r ∈ S.rounds, r.entry.work < 256
  /-- the roots fit the items -/
  roots : RootsFit (rds S)
  /-- the number of rounds fits its word -/
  len   : (rds S).length < 2 ^ 64
  /-- the salt's words fit their byte -/
  salt  : S.plan.salt / 8 < 2 ^ 8

variable {Bd : Type} (B : BodyD Bd) (D : XD) (Lf : LeafD D B) (dec : View → Bool) (pd : Dig 256)
  (hcfg : D.base.cfg.size = 32) (V : StmInv D)

/-- The test on a chain query: `fitsC` at the data of the description and pd. -/
abbrev PqX : FbIn 256 (D.L Bd dec) .link → Bool :=
  fitsC (pageXPd dec pd B Lf (D.K + 1) hcfg V) (.fb .link)

/-- The test on a leaf query: `fitsC` at the data of the description and pd. -/
abbrev PlX : LeafIn (D.L Bd dec) → Bool := fitsC (pageXPd dec pd B Lf (D.K + 1) hcfg V) .leaf

variable (Bd) in
/-- How the verifier carries a plain part over to the interface. -/
abbrev embX : PlainPart (Twin.up (SOf D.C D.ds)) (Twin.allLo (SOf D.C D.ds)) → PBX Bd D dec :=
  embPX Bd D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())

/-- The wiring of the protocol: the sibling's `wqX` at the description. -/
abbrev wX : ProtocolQueryLayout 256 (D.K + 1) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up :=
  wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec

/-! ## Chain queries -/

/-- A chain query of a round behind the first passes the test, if its chain value has 256 bits,
its plain part belongs to the rounds behind the first (`.inr pl`) and fits round i there (`okL`),
and the numbers are within the words' bounds. -/
theorem later_fitsX (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256)
    (i : ℕ) (ρ : Bits) (rt : List (Dig 256)) (pl : PBL D.C D.ds) (hρ : ρ.length = 256)
    (hi : i + 1 < 2 ^ 64) (hk : okL D.C D.ds i rt pl = true) :
    PqX B D Lf dec pd hcfg V ⟨i + 1, .f2 none ρ, rt, .inr pl⟩ = true := by
  show fitsC (pageXPd dec pd B Lf (D.K + 1) hcfg V) (.fb .link) _ = true
  rw [fitsC_fb, if_neg (Nat.succ_ne_zero i), List.all_eq_true]
  intro j _
  refine fitsQ_put Bd D.base D.C dec (D.K + 1) ⟨i + 1, .f2 none ρ, rt, .inr pl⟩ ?_ j
  unfold fitsQ
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hρ, hi⟩, kindQ_lt Bd D.base D.C dec _⟩, workQ_lt Bd D.base D.C dec hw _⟩, hK⟩, hk⟩

/-- One step of the sibling's test on the chain, at a local round behind the first, with no
statement. -/
theorem askP_loX {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X)
    (g : Fam (typedOracleFamily lam K (Lf ()))) (t : Tag) (Pq : FbIn lam (Lf ()) t → Bool) (cms : List (Dig lam))
    (salt : Bits) (r : RS) (Ss : List RS) (A : RoundSplits (up Ss))
    (w : WireRB lam K r.up r.lo) (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) :
    askP Lf g id none t Pq cms (none : Option X) salt (r :: Ss) (r.lo, A) (w, W) embP i
      (.loc v) rts (pl, pls) =
      match takeRt w.depthJ.length rts with
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
induction on a suffix of the list of rounds, as in the library's proof for plain chains. -/
theorem askP_tailX (g : Fam (typedOracleFamily 256 (D.K + 1) (D.L Bd dec))) (cms : List (Dig 256))
    (salt : Bits) (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256) :
    ∀ (ds : List RD) (n : ℕ) (embP : PlainPart (uL D.C ds) (allLo (SL D.C ds)) → PBX Bd D dec) (ρ : Bits)
        (rts : List (Dig 256)) (pls : Plains (uL D.C ds)),
      ρ.length = 256 →
      (∀ z, ∃ pl : PBL D.C D.ds,
        embP z = .inr pl ∧
          ∀ k rt, okL D.C D.ds (n + k) rt pl = okL D.C ds k rt (embPL D.C ds z)) →
      RootsFit ds → noncesOK D.C ds pls → n + ds.length < 2 ^ 64 →
      askP (lam := 256) (K := D.K + 1) (fun _ => D.L Bd dec) g id none .link
          (PqX B D Lf dec pd hcfg V)
          cms (none : Option Unit) salt (SL D.C ds) (allLo (SL D.C ds))
          (wiresSL D.C D.K (chalP D.base.plan.field D.K) ds) embP (n + 1) (.loc ρ) rts pls = true
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | d :: ds, n, embP, ρ, rts, (pl, pls), hρ, hemb, hr, hn, hlen => by
    refine (askP_loX (fun _ => D.L Bd dec) g .link (PqX B D Lf dec pd hcfg V) cms salt
      (roundS D.C d) (SL D.C ds) (allLo (SL D.C ds))
      (wireS D.C D.K (chalP D.base.plan.field D.K) d)
      (wiresSL D.C D.K (chalP D.base.plan.field D.K) ds) embP (n + 1) ρ rts pl pls).trans ?_
    cases ht : takeRt (wireS D.C D.K (chalP D.base.plan.field D.K) d).depthJ.length rts with
    | none => rfl
    | some x =>
      obtain ⟨rt, rts'⟩ := x
      obtain ⟨pl', he, hk⟩ := hemb (.inl (.inr pl))
      have hlen' : n + (ds.length + 1) < 2 ^ 64 := hlen
      have hrt : rt.length = d.trees.length :=
        (takeRt_length _ _ _ _ ht).trans (List.length_map _)
      have hfit : PqX B D Lf dec pd hcfg V
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (D.L Bd dec) .link) =
          true := by
        rw [he]
        refine later_fitsX B D Lf dec pd hcfg V hK hw n ρ rt pl' hρ (by omega) ?_
        have := hk 0 rt
        rw [Nat.add_zero] at this
        rw [this]
        exact okRound_of d.entry.work d.items rt pl (hr d List.mem_cons_self rt hrt) hn.1
      show (PqX B D Lf dec pd hcfg V
            (⟨n + 1, .f2 none ρ, rt, embP (.inl (.inr pl))⟩ : FbIn 256 (D.L Bd dec) .link) &&
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

/-- The first chain query passes the test: two roots in its head, none of its own, a salt of 256
bits, a statement of fewer than 2^64 bytes. -/
theorem first_fitsX (cm cm' : Dig 256) (salt : Bits) (hs : salt.length = 256)
    (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64) :
    PqX B D Lf dec pd hcfg V
        (⟨0, .f1 [cm, cm'] none salt, [], embX Bd D dec (.inl (.inr ()))⟩ :
          FbIn 256 (D.L Bd dec) .link) = true := by
  show fitsC (pageXPd dec pd B Lf (D.K + 1) hcfg V) (.fb .link) _ = true
  rw [fitsC_fb, if_pos rfl]
  show ((first0X V).put (pd, some (cm, cm'), salt)).isSome = true
  unfold first0X
  rw [pFirst0_put D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V) pd
    (some (cm, cm')) salt _ rfl hst (Or.inr hs)]
  rfl

/-- Every chain query that the verifier forms passes the test, at every family. -/
theorem askP_allX (g : Fam (typedOracleFamily 256 (D.K + 1) (D.L Bd dec))) (cm cm' : Dig 256) (salt : Bits)
    (hK : D.K + 1 < 2 ^ 48) (hw : ∀ r ∈ D.base.rounds, r.entry.work < 256)
    (hs : salt.length = 256) (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64)
    (hr : RootsFit D.ds) (hlen : D.ds.length < 2 ^ 64)
    (rts : List (Dig 256)) (pls : Plains (uL D.C D.ds)) (hn : noncesOK D.C D.ds pls) :
    askP (lam := 256) (K := D.K + 1) (fun _ => D.L Bd dec) g id none .link
        (PqX B D Lf dec pd hcfg V)
        [cm, cm'] (none : Option Unit) salt (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh (embX Bd D dec) 0 .first rts ((), pls) =
      true := by
  show (PqX B D Lf dec pd hcfg V
        (⟨0, .f1 [cm, cm'] none salt, [], embX Bd D dec (.inl (.inr ()))⟩ :
          FbIn 256 (D.L Bd dec) .link) && _) = true
  rw [first_fitsX B D Lf dec pd hcfg V cm cm' salt hs hst, Bool.true_and]
  refine askP_tailX B D Lf dec pd hcfg V g [cm, cm'] salt hK hw D.ds 0
    (fun z => embX Bd D dec (.inr z)) _ rts pls List.length_ofFn ?_ hr hn (by omega)
  intro z
  exact ⟨embPL D.C D.ds z, rfl, fun k rt => by rw [Nat.zero_add]⟩

/-! ## Leaf queries -/

variable (embS : (p : OPos (Twin.up (SOf D.C D.ds))) → OSym (Twin.up (SOf D.C D.ds)) p → Bd)

/-- TWO: what is asked of the bodies of the chain's own symbols, where the original proves it of
the library's typed code of own leaves, from the trees' numbering and size: the page's code of
bodies writes the body of every own symbol, and no such body is a stored symbol. `embS` is the
embedding that the verifier's wire takes. -/
structure OwnFits : Prop where
  /-- the code writes every own symbol's body -/
  writes    : ∀ p a, (Lf.p.put (embS p a)).isSome = true
  /-- an own symbol's body is no stored symbol -/
  notStored : ∀ p a, B.getE (embS p a) = none

/-- A leaf query on a symbol of the protocol, with a salt of the format's length, passes the
test, under `OwnFits`. -/
theorem own_fitsX (hO : OwnFits B D Lf embS) (p : OPos (Twin.up (SOf D.C D.ds)))
    (a : OSym (Twin.up (SOf D.C D.ds)) p) (salt : Bits)
    (hl : salt.length = 256 + 8 * D.base.plan.salt) :
    PlX B D Lf dec pd hcfg V (⟨embS p a, salt⟩ : LeafIn (D.L Bd dec)) = true := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hO.writes p a)
  have hk : leafOKX D dec B (⟨embS p a, salt⟩ : LeafIn (D.L Bd dec)) = true := by
    show (match B.getE (embS p a) with
      | some _ => startIs D.base.cfg (⟨embS p a, salt⟩ : LeafIn (D.L Bd dec))
      | none => true) = true
    rw [hO.notStored p a]
  have h2 : (pLeafC (pageXPd dec pd B Lf (D.K + 1) hcfg V)).put
      (⟨embS p a, salt⟩ : LeafIn (D.L Bd dec)) =
      some (pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) := by
    show (if leafOKX D dec B (⟨embS p a, salt⟩ : LeafIn (D.L Bd dec)) = true then
      ((if salt.length = 256 + 8 * D.base.plan.salt then
        (Lf.p.put (embS p a)).map fun m =>
          pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)) else none) : Option (List Bool))
      else none) = _
    rw [if_pos hk, if_pos hl, hm]
    rfl
  show ((pLeafC (pageXPd dec pd B Lf (D.K + 1) hcfg V)).put _).isSome = true
  rw [h2]
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
    PlX B D Lf dec pd hcfg V (⟨B.embE op.sym, op.salt⟩ : LeafIn (D.L Bd dec)) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  have hm := pStored_some D.a D.base.plan.salt op.sym
    ⟨h2, by unfold _root_.Fmt.leafPlace; omega, h3⟩
  have hc : (bitsToBytes (op.salt.take 256) == D.base.cfg) = true := by
    rw [h1]
    exact bytes_beq_self _
  have h4 : (pLeafC (pageXPd dec pd B Lf (D.K + 1) hcfg V)).put
      (⟨B.embE op.sym, op.salt⟩ : LeafIn (D.L Bd dec)) =
      some (pre33 ++ (op.salt.take 256 ++
        (storedStr D.a D.base.plan.salt op.sym ++ op.salt.drop 256))) := by
    refine (pLeafC_stored _ (storedIn_pageXPd dec pd B Lf (D.K + 1) hcfg V) op.sym op.salt).trans
      ?_
    show (if (bitsToBytes (op.salt.take 256) == D.base.cfg) = true then
      (if op.salt.length = 256 + 8 * D.base.plan.salt then
        ((pStored D.a D.base.plan.salt).put op.sym).map
          (fun m => pre33 ++ (op.salt.take 256 ++ (m ++ op.salt.drop 256)))
      else none)
    else none) = _
    rw [if_pos hc, if_pos hl, hm]
    rfl
  show ((pLeafC (pageXPd dec pd B Lf (D.K + 1) hcfg V)).put _).isSome = true
  rw [h4]
  rfl

/-- Every check that the verifier collects over external positions holds the symbol and the salt of
an opening that the argument string has at one of these positions. -/
theorem extWP_inp {I X : Type} {lam : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) {E : ExtSpec} (we : WireE E)
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

/-- On such a string every query that the verifier forms passes the tests, at every family g. In
the sibling's terms `askedP .. = true`: every chain query passes `PqX`; the chain never joins, so no
oracle of a request tree is asked; where the strict format holds, every leaf query passes `PlX`.
Where it fails, the verifier refuses before it asks a leaf. A vertex's query is two digests and has
no test. Asked: `FitsS D.base D.K`, `OwnFits` and `TypedOK`. -/
theorem askedX (F : FitsS D.base D.K) (hO : OwnFits B D Lf embS)
    (g : Fam (typedOracleFamily 256 (D.K + 1) (D.L Bd dec))) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) (T : TypedOK D dec cm cm' π) :
    askedP (lam := 256) (K := D.K + 1) (fun _ => D.L Bd dec) g id none
      (256 + 8 * D.base.plan.salt) 256 .link (PqX B D Lf dec pd hcfg V)
      (PlX B D Lf dec pd hcfg V)
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec) embS
      (embX Bd D dec) (fun _ => none) B.embE 0 [cm, cm'] () π = true := by
  unfold askedP
  rw [Bool.and_eq_true]
  refine ⟨askP_allX B D Lf dec pd hcfg V g cm cm' π.salt F.k48 F.work T.salt T.stm F.roots F.len
    π.roots π.plains.2 T.nonces, ?_⟩
  cases hc : chainP (lam := 256) (K := D.K + 1) (fun _ => D.L Bd dec) g id none .link [cm, cm']
      (none : Option Unit) π.salt π.rtreq (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh (embX Bd D dec) 0 .first π.roots
      π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    show (!strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
          (wX D dec) 0 () π ρ rts ph || _) = true
    by_cases hst : strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
        (wX D dec) 0 () π ρ rts ph = true
    · rw [hst, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have := chainP_local (fun _ => D.L Bd dec) g id none .link [cm, cm']
          (none : Option Unit) π.salt π.rtreq (SOf D.C D.ds) (wX D dec).sh
          (embX Bd D dec) 0 .first π.roots π.plains (ρ, rts, ph) rfl hc
        rw [show ph.slotVal = none from this]
        rfl
      · cases hf : forestsOfP (fun _ => D.L Bd dec) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
            (wX D dec) embS B.embE [cm, cm'] () π ρ rts with
        | none => rfl
        | some Fs =>
          show ((flatP (fun _ => D.L Bd dec) Fs).all fun c =>
            PlX B D Lf dec pd hcfg V c.inp) = true
          rw [List.all_eq_true]
          intro c hcm
          simp only [strictP, Bool.and_eq_true] at hst
          have h3 := hst.1.1.1.1.2
          have h4 := hst.1.1.1.2
          simp only [forestsOfP] at hf
          split at hf
          · rename_i a b e1 e2
            rw [← Option.some.inj hf, flatP_append] at hcm
            rcases List.mem_append.1 hcm with hcm | hcm
            · obtain ⟨p, s, salt, i1, i2⟩ := forestsP_inp (fun _ => D.L Bd dec)
                (256 + 8 * D.base.plan.salt) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
                (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh _ rts _ π.opens a e1 h3 c hcm
              rw [i1]
              exact own_fitsX B D Lf dec pd hcfg V embS hO p s salt i2
            · unfold forestExtP at e2
              obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 e2
              obtain ⟨x, hx, rfl⟩ :=
                List.mem_map.1 (mem_flat_split (fun _ => D.L Bd dec) _ _ c hcm)
              obtain ⟨p, hp, op, ho, i1⟩ :=
                extWP_inp (fun _ => D.L Bd dec) _ _ _ _ _ _ cs hcs x hx
              rw [i1]
              have hl : op.salt.length = 256 + 8 * D.base.plan.salt := by
                unfold sExtP strictExt at h4
                have := List.all_eq_true.1 h4 p hp
                rw [ho] at this
                simp only [Bool.and_eq_true, decide_eq_true_eq] at this
                exact this.2
              exact stored_fitsX B D Lf dec pd hcfg V F.salt op (T.ext p op ho) hl
          · cases hf
    · rw [Bool.not_eq_true] at hst
      rw [hst]
      rfl

/-! ## The verifier at the two families -/

/-- THE EVALUABLE FORM OF THE COMPILED VERIFIER, AT famXPd AND AT WHAT THE ENCODING READS OUT OF
g. For a description with `FitsS`, bodies with `OwnFits`, an argument string with `TypedOK`, and
every g. An equation between two runs: of neither is it said that it accepts. Nothing on soundness;
no probability. -/
theorem verifyP_readX (F : FitsS D.base D.K) (hO : OwnFits B D Lf embS) (g : Fam (rom 256))
    (cm cm' : Dig 256) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (T : TypedOK D dec cm cm' π) :
    verifyP (fun _ => D.L Bd dec) (famXPd B D dec (digToBytes pd) (oB (g ())) (D.K + 1)) id none
        (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec)
        embS (embX Bd D dec) (fun _ => none) B.embE 0 [cm, cm'] () π =
      verifyP (fun _ => D.L Bd dec)
        (readBlocks (theImpl (pageXPd dec pd B Lf (D.K + 1) hcfg V)) g) id none
        (256 + 8 * D.base.plan.salt) 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (wX D dec)
        embS (embX Bd D dec) (fun _ => none) B.embE 0 [cm, cm'] () π := by
  have hw : FrontBlind (lam := 256) (K := D.K + 1) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann (wX D dec).sh :=
    fun _ _ => Subsingleton.elim _ _
  refine verifyP_asked (fun _ => D.L Bd dec) _ _ id none _ 256 .link
    (PqX B D Lf dec pd hcfg V) (PlX B D Lf dec pd hcfg V) ?_ ?_ ?_ (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
    (wX D dec) hw _ _ _ _ 0 [cm, cm'] () π (askedX B D Lf dec pd hcfg V embS F hO _ cm cm' π T)
  · intro q hq
    exact ⟨famXPd_last_read dec pd B Lf (D.K + 1) (Nat.succ_pos _) hcfg V g q hq,
      famXPd_whole_read dec pd B Lf (D.K + 1) (Nat.succ_pos _) hcfg V g q hq⟩
  · intro q hq
    exact famXPd_leaf_read dec pd B Lf (D.K + 1) (Nat.succ_pos _) hcfg V g q hq
  · intro a b
    exact famXPd_node_read dec pd B Lf (D.K + 1) (Nat.succ_pos _) hcfg V g a b

/-- THE RUN OF THE COMPILED VERIFIER, AT famXPd AND AT WHAT THE ENCODING READS OUT OF g. The
same for the sibling's `verifyOneProtocol` itself. An equation between two runs: of neither is it said that
it accepts. Nothing on soundness; no probability. -/
theorem verifyBS_readX (F : FitsS D.base D.K) (hO : OwnFits B D Lf embS) (g : Fam (rom 256))
    (cm cm' : Dig 256) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (T : TypedOK D dec cm cm' π) :
    (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L Bd dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) embS
        (embX Bd D dec) (fun _ => none) B.embE 0 [cm, cm'] () π).det
        (famXPd B D dec (digToBytes pd) (oB (g ())) (D.K + 1)) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L Bd dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) embS
        (embX Bd D dec) (fun _ => none) B.embE 0 [cm, cm'] () π).det
        (readBlocks (theImpl (pageXPd dec pd B Lf (D.K + 1) hcfg V)) g) := by
  rw [← thin_verify Unit Unit 256 _ (D.L Bd dec) (famXPd B D dec (digToBytes pd) (oB (g ()))
      (D.K + 1)) Unit _ _ 256 .link
      _ _ _ _ (fun _ => none) B.embE 0 _ () π,
    ← thin_verify Unit Unit 256 _ (D.L Bd dec)
      (readBlocks (theImpl (pageXPd dec pd B Lf (D.K + 1) hcfg V)) g)
      Unit _ _ 256 .link _ _ _ _ (fun _ => none) B.embE 0 _ () π]
  exact verifyP_readX B D Lf dec pd hcfg V embS F hO g cm cm' π T

end TypedOracleCompiler.Run.PQ
