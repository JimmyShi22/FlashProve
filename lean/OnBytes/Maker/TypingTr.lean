-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingTr.lean: the transcript that the compiled verifier builds from the typed string
of a whole file (OnBytes/Maker/TypingW.lean), cut chain by chain.

The compiled verifier (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) decides at the transcript `mkTr`:
the string's plain parts where a component is sent, its verifier's messages, and the opened symbols
where the tree of a position has a root. The decision of a file (OnBytes/Maker/Whole.lean) cuts that
transcript into the three chains' stretches and forms a view of each.

1. For any rounds G of a file and any wire records of its six parts: the three stretches of `mkTr`
   over the whole are `mkTr` over each stretch, at the cuts of the roots, the plain parts, the
   verifier's messages and the openings (`tr₁_mkTr`, `tr₂_mkTr`, `tr₃_mkTr`).
2. For a stretch of written rounds, local (`wiresLo`) or shared (`wiresSh`): if in every round the
   component that the round sends has as many roots as the round has trees (`SentLo`, `SentSh`),
   then `mkTr` has the string's plain parts (`plains_lo`, `plains_sh`) and answers with the symbol
   of each opening that the string holds (`read_lo`, `read_sh`). Its verifier's messages are those
   put in (the compiler's `mkTr_rho`).
3. That property follows, stretch by stretch, from two properties of the roots over the whole file
   (`sent_of_flags`): as many roots as trees in each component sent (`RtFlagsAll`,
   OnBytes/TypedOracleCompiler/Joined/Clauses.lean) and the component of each round's kind sent (`SentK`). A run of
   a chain yields the second (`sentK_of_runsIn`) and, by Clauses.lean, the first.
4. At a string laid together from three chains' strings, as `FileW.assemble` of
   OnBytes/TypedOracleCompiler/Joined/Assemble.lean lays them (`plainsA`, `opensA`): its cuts are the three strings'
   own parts (`plA₁` .. `opA₃`), so each chain's stretch of the whole transcript is the transcript
   over that stretch from that chain's own string (`tr₁_assembled`, `tr₂_assembled`,
   `tr₃_assembled`). At the typed strings of a file these are the transcripts of part 2 at the
   stretches' typed parts (`tr₁_typed`, `tr₂_typed`, `tr₃_typed`), and what the typing of a whole
   file returns has this form (`toBPrfW_parts`).
5. Where the three chains are run one after the other (OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean): their
   three transcripts in a row are the transcript over the whole (`three_eq_mkTr`), and what the
   three runs yield meets the premises of `sent_of_flags` (`flags_of_three`).

Not claimed. That the verifier's messages hold the draws that the reader has read. What the tables
hold. Nothing on hashes, paths or salts; nothing on
soundness.


-/
import OnBytes.Maker.TypingW
import OnBytes.Maker.TypingTLaws
import OnBytes.Maker.TypingTWire
import OnBytes.Maker.WireLaws
import OnBytes.TypedOracleCompiler.Joined.Clauses
import OnBytes.TypedOracleCompiler.Joined.YesByCuts

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag RunsIn)
open _root_.Run _root_.Run.PQ

/-! ## 1. The three stretches of the transcript over the whole -/

section Cuts
variable {lam K : ℕ} (G : Chains)

/-- the roots that the chain has yielded for chain 1's rounds behind the front -/
def rtS₁ (R : RootsOfChain lam G.sh) : RootsOfChain lam G.s₁ := RT.fst R.2
/-- from the joining round on -/
def rtSJ (R : RootsOfChain lam G.sh) : RootsOfChain lam G.shJ := RT.snd (s := G.s₁) R.2
/-- for chain 2's rounds behind the joining round -/
def rtS₂ (R : RootsOfChain lam G.sh) : RootsOfChain lam G.s₂ := RT.fst (rtSJ G R).2
/-- for chain 3's rounds behind the seam -/
def rtS₃ (R : RootsOfChain lam G.sh) : RootsOfChain lam G.s₃ := (RT.snd (s := G.s₂) (rtSJ G R).2).2

/-- the openings at the positions of chain 1's rounds behind the front -/
def opS₁ (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p))) :
    (p : OPos G.s₁) → Option (Opening lam (OSym G.s₁ p)) :=
  opensL (s := G.s₁) (u := G.shJ) fun p => f (.inr p)
/-- from the joining round on -/
def opSJ (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p))) :
    (p : OPos G.shJ) → Option (Opening lam (OSym G.shJ p)) :=
  opensR (s := G.s₁) (u := G.shJ) fun p => f (.inr p)
/-- at the positions of chain 2's rounds behind the joining round -/
def opS₂ (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p))) :
    (p : OPos G.s₂) → Option (Opening lam (OSym G.s₂ p)) :=
  opensL (s := G.s₂) (u := G.sh₃) fun p => opSJ G f (.inr p)
/-- at the positions of chain 3's rounds behind the seam -/
def opS₃ (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p))) :
    (p : OPos G.s₃) → Option (Opening lam (OSym G.s₃ p)) :=
  fun p => opensR (s := G.s₂) (u := G.sh₃) (fun q => opSJ G f (.inr q)) (.inr p)

variable {G} (V : Wires lam K G) (R : RootsOfChain lam G.sh) (pls : Plains G.sh) (ρ : Rho G.sh)
  (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p)))

theorem tr₁_mkTr :
    G.tr₁ (mkTr G.sh G.ann V.sh R pls ρ f) =
      mkTr G.s₁ (RoundSplits.allLocal G.s₁) V.W₁ (rtS₁ G R) (G.pl₁ pls) (G.rho₁ ρ) (opS₁ G f) := by
  obtain ⟨rt, R⟩ := R
  obtain ⟨pl, pls⟩ := pls
  obtain ⟨c, ρ⟩ := ρ
  show Tr.fst (mkTr (G.s₁ ++ G.shJ) (RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ)
    (WireSB.app V.W₁ V.shJ) R pls ρ fun p => f (.inr p)) = _
  rw [mkTr_app, Tr.fst_app, WireSB.fst_app]
  rfl

theorem trJ_mkTr :
    G.trJ (mkTr G.sh G.ann V.sh R pls ρ f) =
      mkTr G.shJ G.annJ V.shJ (rtSJ G R) (G.plJ' pls) (G.rhoJ ρ) (opSJ G f) := by
  obtain ⟨rt, R⟩ := R
  obtain ⟨pl, pls⟩ := pls
  obtain ⟨c, ρ⟩ := ρ
  show Tr.snd (s := G.s₁) (mkTr (G.s₁ ++ G.shJ) (RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ)
    (WireSB.app V.W₁ V.shJ) R pls ρ fun p => f (.inr p)) = _
  rw [mkTr_app, Tr.snd_app, WireSB.snd_app]
  rfl

theorem tr₂_mkTr :
    G.tr₂ (mkTr G.sh G.ann V.sh R pls ρ f) =
      mkTr G.s₂ (RoundSplits.const (RAnn.ofShared .sh) G.s₂) V.W₂ (rtS₂ G R) (G.pl₂ pls) (G.rho₂ ρ)
        (opS₂ G f) := by
  unfold Chains.tr₂
  rw [trJ_mkTr]
  generalize rtSJ_eq : rtSJ G R = RJ
  generalize plJ_eq : G.plJ' pls = plJ
  generalize rhoJ_eq : G.rhoJ ρ = ρJ
  generalize opSJ_eq : opSJ G f = fJ
  have e1 : rtS₂ G R = RT.fst RJ.2 := by rw [← rtSJ_eq]; rfl
  have e2 : G.pl₂ pls = Plains.fst plJ.2 := by rw [← plJ_eq]; rfl
  have e3 : G.rho₂ ρ = Rho.fst ρJ.2 := by rw [← rhoJ_eq]; rfl
  have e4 : opS₂ G f = opensL (s := G.s₂) (u := G.sh₃) fun p => fJ (.inr p) := by
    rw [← opSJ_eq]; rfl
  rw [e1, e2, e3, e4]
  obtain ⟨rt, RJ⟩ := RJ
  obtain ⟨pl, plJ⟩ := plJ
  obtain ⟨c, ρJ⟩ := ρJ
  show Tr.fst (mkTr (G.s₂ ++ G.sh₃) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃)
    (WireSB.app V.W₂ V.sh₃) RJ plJ ρJ fun p => fJ (.inr p)) = _
  rw [mkTr_app, Tr.fst_app, WireSB.fst_app]

theorem tr₃_mkTr :
    G.tr₃ (mkTr G.sh G.ann V.sh R pls ρ f) =
      mkTr G.s₃ (RoundSplits.allLocal G.s₃) V.W₃ (rtS₃ G R) (G.pl₃ pls) (G.rho₃ ρ) (opS₃ G f) := by
  unfold Chains.tr₃
  rw [trJ_mkTr]
  generalize rtSJ_eq : rtSJ G R = RJ
  generalize plJ_eq : G.plJ' pls = plJ
  generalize rhoJ_eq : G.rhoJ ρ = ρJ
  generalize opSJ_eq : opSJ G f = fJ
  have e1 : rtS₃ G R = (RT.snd (s := G.s₂) RJ.2).2 := by rw [← rtSJ_eq]; rfl
  have e2 : G.pl₃ pls = (Plains.snd (s := G.s₂) plJ.2).2 := by rw [← plJ_eq]; rfl
  have e3 : G.rho₃ ρ = (Rho.snd (s := G.s₂) ρJ.2).2 := by rw [← rhoJ_eq]; rfl
  have e4 : opS₃ G f =
      fun p => opensR (s := G.s₂) (u := G.sh₃) (fun q => fJ (.inr q)) (.inr p) := by
    rw [← opSJ_eq]; rfl
  rw [e1, e2, e3, e4]
  obtain ⟨rt, RJ⟩ := RJ
  obtain ⟨pl, plJ⟩ := plJ
  obtain ⟨c, ρJ⟩ := ρJ
  show (Tr.snd (s := G.s₂) (mkTr (G.s₂ ++ G.sh₃)
    (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃)
    (WireSB.app V.W₂ V.sh₃) RJ plJ ρJ fun p => fJ (.inr p))).2.2 = _
  rw [mkTr_app, Tr.snd_app, WireSB.snd_app]
  rfl

end Cuts

/-! ## 2. A stretch of written rounds -/

/-- Where the tree of a position of the first round has a root and the string holds an opening, the
transcript's oracle message holds the opening's symbol. -/
theorem mkTr_head {lam K : ℕ} (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (rt : RtC lam × RtC lam) (R : RootsOfChain lam s)
    (pl : r.Plain) (pls : Plains s) (c : r.Chal) (ρ : Rho s)
    (f : (p : OPos (r :: s)) → Option (Opening lam (OSym (r :: s) p))) (p : r.Pos)
    (op : Opening lam (r.Sym p)) (h1 : rootAt w rt p = true) (h2 : f (.inl p) = some op) :
    r.rd (mkTr (r :: s) (a, A) (w, W) (rt, R) (pl, pls) (c, ρ) f).1.1 p = op.sym := by
  simp only [mkTr]
  rw [w.pt.rd_ofSyms, h1, h2]

section Stretch
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- In every round the slot's component is sent, with as many roots as the round has trees. -/
def SentLo : (ds : List RDT) → RootsOfChain 256 (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (rt, R) => (∃ l, rt.2 = some l ∧ l.length = d.trees.length) ∧ SentLo ds R

/-- In every round the shared component is sent, with as many roots as the round has trees. -/
def SentSh : (ds : List RDT) → RootsOfChain 256 (uLT C ds) → Prop
  | [], _ => True
  | d :: ds, (rt, R) => (∃ l, rt.1 = some l ∧ l.length = d.trees.length) ∧ SentSh ds R

theorem treeT_lt (ts : List Fmt.Shape) (p : PosT ts) : treeT ts p < ts.length :=
  treeIn_eq ts p ▸ treeIn_lt ts p

theorem effPlains_lo :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds)), SentLo C ds R →
      effPlains (uLT C ds) (RoundSplits.allLocal (uLT C ds)) R pl = pl
  | [], _, _, _ => rfl
  | d :: ds, (rt, R), (p, pl), ⟨⟨l, hl, _⟩, h⟩ => by
      show (effPlain (RAnn.allLocal (roundT C d).up) rt p,
        effPlains (uLT C ds) (RoundSplits.allLocal (uLT C ds)) R pl) = (p, pl)
      rw [effPlains_lo ds R pl h]
      refine congrArg (fun z => (z, pl)) ?_
      unfold effPlain
      rw [hl]
      rfl

theorem effPlains_sh :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds)), SentSh C ds R →
      effPlains (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) R pl = pl
  | [], _, _, _ => rfl
  | d :: ds, (rt, R), (p, pl), ⟨⟨l, hl, _⟩, h⟩ => by
      show (effPlain (RAnn.ofShared .sh (roundT C d).up) rt p,
        effPlains (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) R pl) = (p, pl)
      rw [effPlains_sh ds R pl h]
      refine congrArg (fun z => (z, pl)) ?_
      unfold effPlain
      rw [hl]
      rfl

/-- **The plain parts of the transcript are the string's**, at local rounds. -/
theorem plains_lo (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds))
    (ρ : Rho (uLT C ds)) (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
    (h : SentLo C ds R) :
    (mkTr (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R pl ρ f).plains = pl := by
  rw [mkTr_plains, effPlains_lo C ds R pl h]

/-- The same at shared rounds. -/
theorem plains_sh (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds))
    (ρ : Rho (uLT C ds)) (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
    (h : SentSh C ds R) :
    (mkTr (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) R pl ρ
      f).plains = pl := by
  rw [mkTr_plains, effPlains_sh C ds R pl h]

/-- **The transcript answers with the symbol of each opening that the string holds**, at local
rounds. -/
theorem read_lo :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
      (p : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) p)), SentLo C ds R →
      f p = some op →
      (mkTr (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R pl ρ f).read p = op.sym
  | d :: ds, (rt, R), (pl, pls), (c, ρ), f, .inl q, op, ⟨⟨l, hl, hn⟩, _⟩, hf => by
      have hr : rootAt (wireLo C K chal d) rt q = true := by
        show ((rt.2.getD [])[treeT d.trees q]?).isSome = true
        rw [hl]
        show (l[treeT d.trees q]?).isSome = true
        rw [List.getElem?_eq_getElem (hn ▸ treeT_lt d.trees q)]
        rfl
      exact mkTr_head (roundT C d).up (uLT C ds) _ _ (wireLo C K chal d) (wiresLo C K chal ds) rt R
        pl pls c ρ f q op hr hf
  | _ :: ds, (_, R), (_, pls), (_, ρ), f, .inr q, op, ⟨_, h⟩, hf =>
      read_lo ds R pls ρ (fun p => f (.inr p)) q op h hf

/-- The same at shared rounds. -/
theorem read_sh :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))
      (f : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
      (p : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) p)), SentSh C ds R →
      f p = some op →
      (mkTr (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) R pl ρ
        f).read p = op.sym
  | d :: ds, (rt, R), (pl, pls), (c, ρ), f, .inl q, op, ⟨⟨l, hl, hn⟩, _⟩, hf => by
      have hr : rootAt (wireSh C K chal d) rt q = true := by
        show ((rt.1.getD [])[treeT d.trees q]?).isSome = true
        rw [hl]
        show (l[treeT d.trees q]?).isSome = true
        rw [List.getElem?_eq_getElem (hn ▸ treeT_lt d.trees q)]
        rfl
      exact mkTr_head (roundT C d).up (uLT C ds) _ _ (wireSh C K chal d) (wiresSh C K chal ds) rt R
        pl pls c ρ f q op hr hf
  | _ :: ds, (_, R), (_, pls), (_, ρ), f, .inr q, op, ⟨_, h⟩, hf =>
      read_sh ds R pls ρ (fun p => f (.inr p)) q op h hf

end Stretch

/-! ## 3. What a run of the chain yields -/

section Sent
variable {lam K : ℕ}

/-- In every round the component that the round's kind names is sent: the slot's in a local round,
the shared one in a shared round. -/
def SentK : (s : Shape) → RoundSplits s → RootsOfChain lam s → Prop
  | [], _, _ => True
  | _ :: s, (a, A), (rt, R) =>
    (a.kind = .lo → rt.2.isSome = true) ∧ (a.kind = .sh → rt.1.isSome = true) ∧ SentK s A R

theorem sentK_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (R : RootsOfChain lam (s ++ u)),
    SentK (s ++ u) (RoundSplits.app A B) R ↔ SentK s A (RT.fst R) ∧ SentK u B (RT.snd (s := s) R)
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, _), _, (_, R) =>
    have h := sentK_app R
    ⟨fun z => ⟨⟨z.1, z.2.1, (h.1 z.2.2).1⟩, (h.1 z.2.2).2⟩,
      fun z => ⟨z.1.1, z.1.2.1, h.2 ⟨z.1.2.2, z.2⟩⟩⟩

/-- What a run of the chain yields has the component of each round's kind. -/
theorem sentK_of_runsIn {I X : Type} {L : BatchProtocolWithLeafBody I X} {tr : Trace (typedOracleFamily lam K L)} {t : Tag}
    {cms : List (Dig lam)} {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (i : ℕ)
        (ph ph' : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      SentK s A R
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (_, W), _, _, _, ph', _, (_, pls), (_, ρ), (_, R), h => by
      obtain ⟨_, _, ph₁, rts', hv, _, _, h', _⟩ := runsIn_chainB_cons_flags h
      have ih := sentK_of_runsIn s A W _ _ ph₁ ph' rts' pls ρ R h'
      cases hv with
      | f1 root ans hk => exact ⟨fun _ => rfl, fun e => (by cases hk.symm.trans e), ih⟩
      | f2 ρ root ans hk => exact ⟨fun _ => rfl, fun e => (by cases hk.symm.trans e), ih⟩
      | join ρ rtj rt0 c ans hk hg => exact ⟨fun _ => rfl, fun _ => rfl, ih⟩
      | f5 ρ0 c root ans hk => exact ⟨fun e => (by cases hk.symm.trans e), fun _ => rfl, ih⟩
      | f3 ρ0 c root ans hk => exact ⟨fun _ => rfl, fun e => (by cases hk.symm.trans e), ih⟩
      | f2' ρ c root ans hk => exact ⟨fun _ => rfl, fun e => (by cases hk.symm.trans e), ih⟩

end Sent

section SentT
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem sentLo_of : ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)),
    RtFlagsAll (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R →
    SentK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) R → SentLo C ds R
  | [], _, _, _ => trivial
  | d :: ds, (rt, R), ⟨hf, hF⟩, ⟨h1, _, hK⟩ => by
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h1 rfl)
      have e : l.length = (d.trees.map (·.a)).length := (hf.2 l hl).1
      exact ⟨⟨l, hl, by rw [e, List.length_map]⟩, sentLo_of ds R hF hK⟩

theorem sentSh_of : ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)),
    RtFlagsAll (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) R →
    SentK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) R → SentSh C ds R
  | [], _, _, _ => trivial
  | d :: ds, (rt, R), ⟨hf, hF⟩, ⟨_, h1, hK⟩ => by
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h1 rfl)
      have e : l.length = (d.trees.map (·.a)).length := (hf.1 l hl).1
      exact ⟨⟨l, hl, by rw [e, List.length_map]⟩, sentSh_of ds R hF hK⟩

variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- Over the whole file: as many roots as trees in each component that is sent, and the component of
each round's kind sent, give the property of part 2 for each of the three stretches. -/
theorem sent_of_flags (R : RootsOfChain 256 (chainsOf C D tF tJ t3).sh)
    (hF : RtFlagsAll (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh R)
    (hK : SentK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann R) :
    SentLo C D.ds₁ (rtS₁ (chainsOf C D tF tJ t3) R) ∧
      SentSh C D.ds₂ (rtS₂ (chainsOf C D tF tJ t3) R) ∧
      SentLo C D.ds₃ (rtS₃ (chainsOf C D tF tJ t3) R) := by
  obtain ⟨rt, R⟩ := R
  have f1 := (rtFlags_app (A := RoundSplits.allLocal (uLT C D.ds₁)) (B := (chainsOf C D tF tJ t3).annJ)
    (WireSB.app (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ) R).1 hF.2
  have k1 := (sentK_app (A := RoundSplits.allLocal (uLT C D.ds₁)) (B := (chainsOf C D tF tJ t3).annJ)
    R).1 hK.2.2
  rw [WireSB.fst_app, WireSB.snd_app] at f1
  refine ⟨sentLo_of C K chal D.ds₁ _ f1.1 k1.1, ?_⟩
  show SentSh C D.ds₂ (RT.fst (RT.snd (s := uLT C D.ds₁) R).2) ∧
    SentLo C D.ds₃ (RT.snd (s := uLT C D.ds₂) (RT.snd (s := uLT C D.ds₁) R).2).2
  generalize RT.snd (s := uLT C D.ds₁) R = RJ at f1 k1
  obtain ⟨rtJ, RJ⟩ := RJ
  have f2 := (rtFlags_app (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
    (B := (chainsOf C D tF tJ t3).ann₃)
    (WireSB.app (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃) RJ).1 f1.2.2
  have k2 := (sentK_app (A := RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
    (B := (chainsOf C D tF tJ t3).ann₃) RJ).1 k1.2.2.2
  rw [WireSB.fst_app, WireSB.snd_app] at f2
  refine ⟨sentSh_of C K chal D.ds₂ _ f2.1 k2.1, ?_⟩
  show SentLo C D.ds₃ (RT.snd (s := uLT C D.ds₂) RJ).2
  generalize RT.snd (s := uLT C D.ds₂) RJ = R3 at f2 k2
  obtain ⟨rt3, R3⟩ := R3
  exact sentLo_of C K chal D.ds₃ _ f2.2.2 k2.2.2.2

end SentT

/-! ## 4. The cuts of a string laid together from three chains' strings -/

section Assembled
variable {lam K : ℕ} (G : Chains) (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂)
  (k₃ : ChainStr lam G.c₃)

/-- The plain parts of the three chains' strings in a row, as `FileW.assemble` lays them. -/
def plainsA : Plains G.sh :=
  Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃) k₁.plains
    (Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains)

/-- Their openings, as `FileW.assemble` lays them. -/
def opensA : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p)) :=
  opensApp (s := G.c₁) (u := G.c₂ ++ G.c₃) k₁.opens
    (opensApp (s := G.c₂) (u := G.c₃) k₂.opens k₃.opens)

theorem plA₁ : G.pl₁ (plainsA G k₁ k₂ k₃) = k₁.plains.2 := by
  obtain ⟨_, ⟨pF, pl₁⟩, _⟩ := k₁
  exact Plains.fst_app _ _

theorem plAJ :
    G.plJ' (plainsA G k₁ k₂ k₃) = Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains := by
  obtain ⟨_, ⟨pF, pl₁⟩, _⟩ := k₁
  exact Plains.snd_app _ _

theorem plA₂ : G.pl₂ (plainsA G k₁ k₂ k₃) = k₂.plains.2 := by
  unfold Chains.pl₂
  rw [plAJ]
  obtain ⟨_, ⟨pJ, pl₂⟩, _⟩ := k₂
  exact Plains.fst_app _ _

theorem plA₃ : G.pl₃ (plainsA G k₁ k₂ k₃) = k₃.plains.2 := by
  unfold Chains.pl₃
  rw [plAJ]
  obtain ⟨_, ⟨pJ, pl₂⟩, _⟩ := k₂
  exact congrArg Prod.snd (Plains.snd_app (s := G.s₂) (t := G.c₃) pl₂ k₃.plains)

theorem opA₁ : opS₁ G (opensA G k₁ k₂ k₃) = fun p => k₁.opens (.inr p) :=
  funext fun p => opensL_app (s := G.s₁) (fun q => k₁.opens (.inr q)) _ p

theorem opAJ :
    opSJ G (opensA G k₁ k₂ k₃) = opensApp (s := G.c₂) (u := G.c₃) k₂.opens k₃.opens :=
  opensR_app (s := G.s₁) (fun q => k₁.opens (.inr q)) _

theorem opA₂ : opS₂ G (opensA G k₁ k₂ k₃) = fun p => k₂.opens (.inr p) := by
  unfold opS₂
  rw [opAJ]
  exact funext fun p => opensL_app (s := G.s₂) (fun q => k₂.opens (.inr q)) _ p

theorem opA₃ : opS₃ G (opensA G k₁ k₂ k₃) = fun p => k₃.opens (.inr p) := by
  unfold opS₃
  rw [opAJ]
  funext p
  exact congrFun (opensR_app (s := G.s₂) (fun q => k₂.opens (.inr q)) k₃.opens) (.inr p)

variable {G} (V : Wires lam K G) (R : RootsOfChain lam G.sh) (ρ : Rho G.sh)

/-- **Chain 1's stretch of the transcript that the compiled verifier builds from the three chains'
strings** is the transcript over that stretch alone, from chain 1's own string. -/
theorem tr₁_assembled :
    G.tr₁ (mkTr G.sh G.ann V.sh R (plainsA G k₁ k₂ k₃) ρ (opensA G k₁ k₂ k₃)) =
      mkTr G.s₁ (RoundSplits.allLocal G.s₁) V.W₁ (rtS₁ G R) k₁.plains.2 (G.rho₁ ρ)
        fun p => k₁.opens (.inr p) := by
  rw [tr₁_mkTr, plA₁, opA₁]

/-- The same for chain 2. -/
theorem tr₂_assembled :
    G.tr₂ (mkTr G.sh G.ann V.sh R (plainsA G k₁ k₂ k₃) ρ (opensA G k₁ k₂ k₃)) =
      mkTr G.s₂ (RoundSplits.const (RAnn.ofShared .sh) G.s₂) V.W₂ (rtS₂ G R) k₂.plains.2 (G.rho₂ ρ)
        fun p => k₂.opens (.inr p) := by
  rw [tr₂_mkTr, plA₂, opA₂]

/-- The same for chain 3. -/
theorem tr₃_assembled :
    G.tr₃ (mkTr G.sh G.ann V.sh R (plainsA G k₁ k₂ k₃) ρ (opensA G k₁ k₂ k₃)) =
      mkTr G.s₃ (RoundSplits.allLocal G.s₃) V.W₃ (rtS₃ G R) k₃.plains.2 (G.rho₃ ρ)
        fun p => k₃.opens (.inr p) := by
  rw [tr₃_mkTr, plA₃, opA₃]

end Assembled

section Typed
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (pF : TF) (pJ : TJ) (p3 : T3) (pl₁ : Plains (uLT C D.ds₁)) (pl₂ : Plains (uLT C D.ds₂))
  (pl₃ : Plains (uLT C D.ds₃)) (tabs : List (ℕ × List (ℕ × Row3)))
  (os₁ os₂ os₃ : List Fmt.RoundOut)

section At
variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (R : RootsOfChain 256 (chainsOf C D tF tJ t3).sh) (ρ : Rho (chainsOf C D tF tJ t3).sh)

/-- **At the typed strings of a file**: chain 1's stretch of the transcript that the compiled
verifier builds is the transcript of part 2 at the stretch's own typed parts. -/
theorem tr₁_typed :
    (chainsOf C D tF tJ t3).tr₁ (mkTr (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wiresOf C K chal D tF tJ t3).sh R
        (plainsA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃)) ρ
        (opensA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃))) =
      mkTr (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)) (wiresLo C K chal D.ds₁)
        (rtS₁ (chainsOf C D tF tJ t3) R) pl₁ ((chainsOf C D tF tJ t3).rho₁ ρ)
        (opensT C D.ds₁ 0 tabs) :=
  tr₁_assembled _ _ _ (wiresOf C K chal D tF tJ t3) R ρ

/-- The same for chain 2. -/
theorem tr₂_typed :
    (chainsOf C D tF tJ t3).tr₂ (mkTr (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wiresOf C K chal D tF tJ t3).sh R
        (plainsA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃)) ρ
        (opensA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃))) =
      mkTr (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂)) (wiresSh C K chal D.ds₂)
        (rtS₂ (chainsOf C D tF tJ t3) R) pl₂ ((chainsOf C D tF tJ t3).rho₂ ρ)
        (opensT C D.ds₂ D.t₁ tabs) :=
  tr₂_assembled _ _ _ (wiresOf C K chal D tF tJ t3) R ρ

/-- The same for chain 3. -/
theorem tr₃_typed :
    (chainsOf C D tF tJ t3).tr₃ (mkTr (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wiresOf C K chal D tF tJ t3).sh R
        (plainsA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃)) ρ
        (opensA _ (str₁ C D tF tJ t3 pF pl₁ tabs os₁) (str₂ C D tF tJ t3 pJ pl₂ tabs os₂)
          (str₃ C D tF tJ t3 p3 pl₃ tabs os₃))) =
      mkTr (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)) (wiresLo C K chal D.ds₃)
        (rtS₃ (chainsOf C D tF tJ t3) R) pl₃ ((chainsOf C D tF tJ t3).rho₃ ρ)
        (opensT C D.ds₃ (D.t₁ + D.t₂) tabs) :=
  tr₃_assembled _ _ _ (wiresOf C K chal D tF tJ t3) R ρ

end At

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- What the typing of a whole file returns: its plain parts and its openings are those of the three
chains' strings in a row, each stretch typed from its own chain's rounds. -/
theorem toBPrfW_parts (ext : (oneExternalString (2 ^ D.a) SgX).Pos → Option (Opening 256 SgX))
    (salt : ByteArray) (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π) :
    ∃ pl₁ pl₂ pl₃, plainsT C D.ds₁ r.first.out.rounds.toList.dropLast = some pl₁ ∧
      plainsT C D.ds₂ r.shared.out.rounds.toList = some pl₂ ∧
      plainsT C D.ds₃ r.second.out.rounds.toList = some pl₃ ∧
      π.plains = plainsA _ (str₁ C D tF tJ t3 pF pl₁ tabs r.first.out.rounds.toList)
        (str₂ C D tF tJ t3 pJ pl₂ tabs r.shared.out.rounds.toList)
        (str₃ C D tF tJ t3 p3 pl₃ tabs r.second.out.rounds.toList) ∧
      π.opens = opensA _ (str₁ C D tF tJ t3 pF pl₁ tabs r.first.out.rounds.toList)
        (str₂ C D tF tJ t3 pJ pl₂ tabs r.shared.out.rounds.toList)
        (str₃ C D tF tJ t3 p3 pl₃ tabs r.second.out.rounds.toList) := by
  unfold toBPrfW at h
  split at h
  · rename_i run₁ pl₁ pl₂ pl₃ _ h1 h2 h3
    cases h
    exact ⟨pl₁, pl₂, pl₃, h1, h2, h3, rfl, rfl⟩
  · cases h

end Typed

/-! ## 5. The three chains run one after the other -/

section Three
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {G : Chains}
  (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch) (π : OneProtocolProof lam D.batch)
  (a : Out lam G.c₁) (b : Out lam G.c₂) (e : Out lam G.c₃)

/-- The three chains' transcripts in a row (OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean, the field `accept` of
`Cuts`) are the transcript over the whole, at what the three chains have yielded, laid in a row. -/
theorem three_eq_mkTr :
    Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) (TypedOracleCompiler.Joined.tr₁ D wq π a)
        (Tr.app (s := G.c₂) (t := G.c₃) (TypedOracleCompiler.Joined.tr₂ D wq π b) (TypedOracleCompiler.Joined.tr₃ D wq π e)) =
      mkTr G.sh G.ann wq.sh (glue a b e).2.1 π.plains (glue a b e).1 π.opens := by
  show _ = mkTr (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
    (RT.app a.2.1 (RT.app b.2.1 e.2.1)) π.plains
    (Rho.app (s := G.c₁) (t := G.c₂ ++ G.c₃) a.1 (Rho.app (s := G.c₂) (t := G.c₃) b.1 e.1))
    π.opens
  rw [mkTr_app, mkTr_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app, Rho.fst_app,
    Rho.snd_app, Rho.fst_app, Rho.snd_app]
  rfl

variable {D wq π a b e} {tr : Trace (typedOracleFamily lam K L)} {t : Tag}
  {embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Y → Option X}
  {cms : List (Dig lam)} {x : Y}

/-- What three runs, each from where the one before ended, yield, laid in a row: as many roots as
trees in each component that is sent, and the component of each round's kind sent. -/
theorem flags_of_three (h₁ : RunsIn tr (run₁ t D wq embP xin cms x π) (some a))
    (h₂ : RunsIn tr (run₂ t D wq embP xin cms x π a) (some b))
    (h₃ : RunsIn tr (run₃ t D wq embP xin cms x π a b) (some e)) :
    RtFlagsAll G.sh G.ann wq.sh (glue a b e).2.1 ∧ SentK G.sh G.ann (glue a b e).2.1 := by
  have f1 : RtFlagsAll G.c₁ G.A₁ (wire₁ wq) a.2.1 := rtFlags_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₁
  have f2 : RtFlagsAll G.c₂ G.A₂ (wire₂ wq) b.2.1 := rtFlags_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₂
  have f3 : RtFlagsAll G.c₃ G.A₃ (wire₃ wq) e.2.1 := rtFlags_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₃
  have k1 : SentK G.c₁ G.A₁ a.2.1 := sentK_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₁
  have k2 : SentK G.c₂ G.A₂ b.2.1 := sentK_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₂
  have k3 : SentK G.c₃ G.A₃ e.2.1 := sentK_of_runsIn _ _ _ _ _ _ _ _ _ _ _ h₃
  constructor
  · show RtFlagsAll (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
      (RT.app a.2.1 (RT.app b.2.1 e.2.1))
    rw [rtFlags_app, rtFlags_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
    exact ⟨f1, f2, f3⟩
  · show SentK (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃))
      (RT.app a.2.1 (RT.app b.2.1 e.2.1))
    rw [sentK_app, sentK_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
    exact ⟨k1, k2, k3⟩

end Three

end OnBytes.Maker
