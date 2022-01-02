(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Strings.String
     ZArith.ZArith.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Syntax.
From MinimalCaps Require Export
     Values.

From stdpp Require Import finite decidable.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.

(*** TERMS ***)

Module MinCapsTermKit <: TermKit.
  Module valuekit := MinCapsValueKit.
  Module Export VAL := Syntax.Values.Values valuekit.

  (* VARIABLES *)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.

  Notation PCtx := (NCtx 𝑿 Ty).
  Notation LCtx := (NCtx 𝑺 Ty).

  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.
  Definition fresh := ctx.fresh (T := Ty).

  (** FUNCTIONS **)
  Inductive Fun : PCtx -> Ty -> Set :=
  | read_reg        : Fun ["rreg" ∶ ty_enum regname ] ty_word
  | read_reg_cap    : Fun ["creg" ∶ ty_enum regname ] ty_cap
  | read_reg_num    : Fun ["nreg" ∶ ty_enum regname ] ty_int
  | write_reg       : Fun ["wreg" ∶ ty_enum regname,
                           "w"  ∶ ty_word
                          ] ty_unit
  | next_pc         : Fun ctx.nil ty_cap
  | update_pc       : Fun ctx.nil ty_unit
  | add_pc          : Fun ["offset" ∶ ty_int] ty_unit
  | read_mem        : Fun ["c"   ∶ ty_cap ] ty_memval
  | write_mem       : Fun ["c"   ∶ ty_cap,
                           "v"   ∶ ty_memval
                          ] ty_unit
  | read_allowed    : Fun ["p"   ∶ ty_perm ] ty_bool
  | write_allowed   : Fun ["p"   ∶ ty_perm ] ty_bool
  | upper_bound     : Fun ["a"   ∶ ty_addr,
                           "e"   ∶ ty_addr
                          ] ty_bool
  | within_bounds   : Fun ["c"   ∶ ty_cap ] ty_bool
  | perm_to_bits    : Fun ["p" ∶ ty_perm] ty_int
  | perm_from_bits  : Fun ["i" ∶ ty_int] ty_perm
  | is_sub_perm     : Fun ["p" ∶ ty_perm, "p'" ∶ ty_perm] ty_bool
  | is_within_range : Fun ["b'" ∶ ty_addr, "e'" ∶ ty_addr,
                           "b" ∶ ty_addr, "e" ∶ ty_addr] ty_bool
  | abs             : Fun ["i" ∶ ty_int] ty_int
  | exec_jr         : Fun ["lv" ∶ ty_lv] ty_bool
  | exec_jalr       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv ] ty_bool
  | exec_j          : Fun ["offset" ∶ ty_int] ty_bool
  | exec_jal        : Fun ["lv" ∶ ty_lv, "offset" ∶ ty_int] ty_bool
  | exec_bnez       : Fun ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_mv         : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_bool
  | exec_ld         : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_sd         : Fun ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_lea        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv] ty_bool
  | exec_restrict   : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv] ty_bool
  | exec_restricti  : Fun ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_subseg     : Fun ["lv" ∶ ty_lv, "hv1" ∶ ty_hv, "hv2" ∶ ty_hv] ty_bool
  | exec_subsegi    : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_isptr      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_addi       : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_add        : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_sub        : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_slt        : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_slti       : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_sltu       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_sltiu      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_getp       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_getb       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_gete       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_geta       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool
  | exec_fail       : Fun ε ty_bool
  | exec_ret        : Fun ε ty_bool
  | exec_instr      : Fun ["i" ∶ ty_instr] ty_bool
  | exec            : Fun ε ty_bool
  | loop            : Fun ε ty_unit
  .

  Inductive FunX : PCtx -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_memval
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "new_value" ∶ ty_memval] ty_unit
  | dI    : FunX ["code" ∶ ty_int] ty_instr
  .

  Inductive Lem : PCtx -> Set :=
  | open_ptsreg                : Lem ["reg" ∶ ty_enum regname]
  | close_ptsreg (R : RegName) : Lem ctx.nil
  | safe_move_cursor           : Lem ["c'" ∶ ty_cap, "c" ∶ ty_cap]
  | safe_sub_perm              : Lem ["c'" ∶ ty_cap, "c" ∶ ty_cap]
  | safe_within_range          : Lem ["c'" ∶ ty_cap, "c" ∶ ty_cap]
  | int_safe                   : Lem ["i" ∶ ty_int]
  | gen_dummy                  : Lem ["c" ∶ ty_cap]
  .

  Definition 𝑭  : PCtx -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : PCtx -> Ty -> Set := FunX.
  Definition 𝑳  : PCtx -> Set := Lem.

  Inductive Reg : Ty -> Set :=
  | pc   : Reg ty_cap
  | reg0 : Reg ty_word
  | reg1 : Reg ty_word
  | reg2 : Reg ty_word
  | reg3 : Reg ty_word.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.

  Instance 𝑹𝑬𝑮_eq_decision : EqDecision (sigT Reg).
  Proof.
    intros xy; eapply 𝑹𝑬𝑮_eq_dec.
  Defined.

  Program Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) := {| enum := [ existT _ pc; existT _ reg0; existT _ reg1; existT _ reg2; existT _ reg3 ]%list |}.
  Next Obligation.
    now eapply (nodup_fixed (H := 𝑹𝑬𝑮_eq_dec)).
  Defined.
  Next Obligation.
    intros x.
    refine (@bool_decide_unpack _ (elem_of_list_dec _ _) _).
    destruct x; now destruct r.
  Qed.

End MinCapsTermKit.

(*** PROGRAM ***)

Module MinCapsProgramKit <: (ProgramKit MinCapsTermKit).
  Module Export TM := Terms MinCapsTermKit.

  Local Coercion stm_exp : Exp >-> Stm.

  Local Notation "'a'"  := (@exp_var _ "a" _ _) : exp_scope.
  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'e'"  := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'hv'" := (@exp_var _ "hv" _ _) : exp_scope.
  Local Notation "'rv'" := (@exp_var _ "rv" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'lv'" := (@exp_var _ "lv" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exn_scope.
  Local Notation "'p'"  := (@exp_var _ "p" _ _) : exp_scope.
  Local Notation "'p1'" := (@exp_var _ "p1" _ _) : exp_scope.
  Local Notation "'p2'" := (@exp_var _ "p2" _ _) : exp_scope.
  Local Notation "'q'"  := (@exp_var _ "q" _ _) : exp_scope.
  Local Notation "'r'"  := (@exp_var _ "r" _ _) : exp_scope.
  Local Notation "'w'"  := (@exp_var _ "w" _ _) : exp_scope.
  Local Notation "'x'"  := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'immediate'" := (@exp_var _ "immediate" _ _) : exp_scope.
  Local Notation "'offset'" := (@exp_var _ "offset" _ _) : exp_scope.

  Local Notation "'c'"  := "c" : string_scope.
  Local Notation "'e'"  := "e" : string_scope.
  Local Notation "'hv'" := "hv" : string_scope.
  Local Notation "'rv'" := "rv" : string_scope.
  Local Notation "'i'"  := "i" : string_scope.
  Local Notation "'lv'" := "lv" : string_scope.
  Local Notation "'n'"  := "n" : string_scope.
  Local Notation "'p'"  := "p" : string_scope.
  Local Notation "'q'"  := "q" : string_scope.
  Local Notation "'r'"  := "r" : string_scope.
  Local Notation "'w'"  := "w" : string_scope.
  Local Notation "'immediate'" := "immediate" : string_scope.
  Local Notation "'offset'" := "offset" : string_scope.

  Notation stm_call_external := stm_foreign.

  Notation "'use' 'lemma' f args" := (stm_lemma f args%arg) (at level 10, f at next level) : exp_scope.
  Notation "'use' 'lemma' f" := (stm_lemma f env.nil) (at level 10, f at next level) : exp_scope.

  (* NOTE: need to wrap s around parentheses when using this notation (not a real let binding!) *)
  Notation "'let*:' '[' perm ',' beg ',' en ',' cur ']' ':=' cap 'in' s" :=
    (stm_match_record capability cap
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
       "cap_permission" perm)
       "cap_begin" beg)
       "cap_end" en)
       "cap_cursor" cur)
    s) (at level 10) : exp_scope.

  Definition fun_read_reg : Stm ["rreg" ∶ ty_enum regname ] ty_word :=
    use lemma open_ptsreg [exp_var "rreg"]%arg ;;
    match: exp_var "rreg" in regname with
    | R0 => let: "x" := stm_read_register reg0 in use lemma (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_read_register reg1 in use lemma (close_ptsreg R1) ;; stm_exp x
    (* | R2 => let: "x" := stm_read_register reg2 in use lemma (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_read_register reg3 in use lemma (close_ptsreg R3) ;; stm_exp x *)
    end.

  Definition fun_read_reg_cap : Stm ["creg" ∶ ty_enum regname ] ty_cap :=
    let: w := call read_reg (exp_var "creg") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c => stm_exp c
    end.

  Definition fun_read_reg_num : Stm ["nreg" ∶ ty_enum regname ] ty_int :=
    let: w := call read_reg (exp_var "nreg") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["wreg" ∶ ty_enum regname,
                                  "w" ∶ ty_word
                                 ] ty_unit :=
    use lemma open_ptsreg [exp_var "wreg"] ;;
    match: exp_var "wreg" in regname with
    | R0 => let: "x" := stm_write_register reg0 (exp_var "w") in use lemma (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_write_register reg1 (exp_var "w") in use lemma (close_ptsreg R1) ;; stm_exp x
    (* | R2 => let: "x" := stm_write_register reg2 (exp_var "w") in use lemma (close_ptsreg R2) ;; stm_exp x *)
    (* | R3 => let: "x" := stm_write_register reg3 (exp_var "w") in use lemma (close_ptsreg R3) ;; stm_exp x *)
    end ;; stm_val ty_unit tt.

  Definition fun_next_pc : Stm ctx.nil ty_cap :=
    let: "c" := stm_read_register pc in
    let*: ["perm" , "beg" , "end" , "cur"] := (exp_var "c") in
      (exp_record capability
         [ exp_var "perm",
           exp_var "beg",
           exp_var "end",
           exp_var "cur" + exp_int 1 ]).

  Definition fun_update_pc : Stm ctx.nil ty_unit :=
    let: "opc" := stm_read_register pc in
    let: "npc" := call next_pc in
    use lemma safe_move_cursor [exp_var "npc", exp_var "opc"] ;;
    stm_write_register pc (exp_var "npc") ;;
    stm_val ty_unit tt.

  Definition fun_add_pc : Stm ["offset" ∶ ty_int ] ty_unit :=
    let: "opc" := stm_read_register pc in
    let*: ["perm", "beg", "end", "cur"] := (exp_var "opc") in
    (let: "npc" := (exp_record capability
                               [ exp_var "perm",
                                 exp_var "beg",
                                 exp_var "end",
                                 exp_var "cur" + exp_var "offset" ]) in
     use lemma safe_move_cursor [exp_var "npc", exp_var "opc"] ;;
     stm_write_register pc (exp_var "npc") ;;
     stm_val ty_unit tt).

  Definition fun_read_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    call is_sub_perm (exp_val (ty_enum permission) R) (exp_var "p").

  Definition fun_write_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    call is_sub_perm (exp_val (ty_enum permission) RW) (exp_var "p").

  (* Definition fun_sub_perm : Stm ["p1" ∶ ty_perm, "p2" ∶ ty_perm] ty_bool := *)
  (*   match: p1 in permission with *)
  (*   | O   => stm_val ty_bool true *)
  (*   | R   => call read_allowed p2 *)
  (*   | RW  => let: "r" := call read_allowed p2 in *)
  (*            let: "w" := call write_allowed p2 in *)
  (*            stm_exp (exp_var "r" && exp_var "w") *)
  (*   end. *)

  Definition fun_within_bounds : Stm ["c" ∶ ty_cap ] ty_bool :=
    let*: ["p", "b", "e", "a"] := (exp_var "c") in
    (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
     (exp_var "b" <= exp_var "a") && exp_var "u").

  Definition fun_upper_bound : Stm ["a" ∶ ty_addr, "e" ∶ ty_addr] ty_bool :=
    a <= e.

  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty_cap.
    Let bool : Ty := ty_bool.
    Let int : Ty := ty_int.
    Let word : Ty := ty_word.

    Definition fun_exec_sd : Stm [hv ∶ ty_hv, lv ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "base_cap" :: cap  := call read_reg_cap lv in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm",
                                       exp_var "beg",
                                       exp_var "end",
                                       exp_var "cursor" + exp_var "immediate"
                                     ] in
       let: w :: ty_word := call read_reg hv in
       use lemma safe_move_cursor [exp_var "c", exp_var "base_cap"] ;;
       call write_mem c w ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_ld : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "base_cap" :: cap  := call read_reg_cap hv in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm",
                                       exp_var "beg",
                                       exp_var "end",
                                       exp_var "cursor" + exp_var "immediate"
                                     ] in
       use lemma safe_move_cursor [exp_var "c", exp_var "base_cap"] ;;
       let: n :: ty_memval := call read_mem c in
       stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
       call write_reg lv (exp_var n) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_lea : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "base_cap" :: cap  := call read_reg_cap (exp_var "lv") in
      let: "offset" :: ty_int := call read_reg_num (exp_var "hv") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "base_cap") in
      (let: "c" :: cap := exp_record capability
                                     [ exp_var "perm",
                                       exp_var "beg",
                                       exp_var "end",
                                       exp_var "cursor" + exp_var "offset"
                                     ] in
       use lemma safe_move_cursor [exp_var "c", exp_var "base_cap"] ;;
       call write_reg (exp_var "lv") (exp_inr (exp_var "c")) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_restrict : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "c" :: cap  := call read_reg_cap (exp_var "lv") in
      let: "n" :: ty_int := call read_reg_num (exp_var "hv") in
      let*: ["p", "beg", "end", "cursor"] := (exp_var "c") in
      (let: "p'" :: ty_perm := call perm_from_bits (exp_var "n") in
       let: "le" :: ty_bool := call is_sub_perm (exp_var "p'") (exp_var "p") in
       stm_assert (exp_var "le") (exp_string "Err: [restrict] tried to increase permission") ;;
       let: "c'" :: cap := exp_record capability
                                      [ exp_var "p'",
                                        exp_var "beg",
                                        exp_var "end",
                                        exp_var "cursor"
                                      ] in
       use lemma safe_sub_perm [exp_var "c'", exp_var "c"] ;;
       call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_restricti : Stm ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      let: "c" :: cap  := call read_reg_cap (exp_var "lv") in
      let: "n" :: ty_int := exp_var "immediate" in
      let*: ["p", "beg", "end", "cursor"] := (exp_var "c") in
      (let: "p'" :: ty_perm := call perm_from_bits (exp_var "n") in
       let: "le" :: ty_bool := call is_sub_perm (exp_var "p'") (exp_var "p") in
       stm_assert (exp_var "le") (exp_string "Err: [restricti] tried to increase permission") ;;
       let: "c'" :: cap := exp_record capability
                                      [ exp_var "p'",
                                        exp_var "beg",
                                        exp_var "end",
                                        exp_var "cursor"
                                      ] in
       use lemma safe_sub_perm [exp_var "c'", exp_var "c"] ;;
       call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_addi : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "v" :: ty_int := call read_reg_num (exp_var "hv") in
      let: "res" :: ty_int := stm_exp (exp_var "v" + exp_var "immediate") in
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      call write_reg (exp_var "lv") (exp_inl (exp_var "res")) ;;
      use lemma int_safe [exp_var "res"] ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_add : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv ] ty_bool :=
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv3") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "res" :: int := stm_exp (exp_var "v1" + exp_var "v2") in
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      use lemma int_safe [exp_var "res"] ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_sub : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv3") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "res" :: int := stm_exp (exp_var "v1" - exp_var "v2") in
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      use lemma int_safe [exp_var "res"] ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_abs : Stm ["i" ∶ ty_int] ty_int :=
      if: exp_var "i" < (exp_val ty_int 0%Z)
      then exp_var "i" * (exp_val ty_int (-1)%Z)
      else exp_var "i".

    Definition fun_exec_slt : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv3") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      (if: exp_var "v1" < exp_var "v2"
       then
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 1%Z)) ;;
         use lemma int_safe [exp_val ty_int 1%Z]
       else
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 0%Z)) ;;
         use lemma int_safe [exp_val ty_int 0%Z]) ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_slti : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "hv") in
      let: "v2" :: int := exp_var "immediate" in
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      (if: exp_var "v1" < exp_var "v2"
       then
         call write_reg (exp_var "lv") (exp_inl (exp_val ty_int 1%Z)) ;;
         use lemma int_safe [exp_val ty_int 1%Z]
       else
         call write_reg (exp_var "lv") (exp_inl (exp_val ty_int 0%Z)) ;;
         use lemma int_safe [exp_val ty_int 0%Z]) ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_sltu : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv3") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "lv2") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := call read_reg_num (exp_var "lv3") in
      let: "uv2" :: int := call abs (exp_var "v2") in
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      (if: exp_var "uv1" < exp_var "uv2"
       then
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 1%Z)) ;;
         use lemma int_safe [exp_val ty_int 1%Z]
       else
         call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 0%Z)) ;;
         use lemma int_safe [exp_val ty_int 0%Z]) ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_sltiu : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: "v1" :: int := call read_reg_num (exp_var "hv") in
      let: "uv1" :: int := call abs (exp_var "v1") in
      let: "v2" :: int := exp_var "immediate" in
      let: "uv2" :: int := call abs (exp_var "v2") in
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      (if: exp_var "uv1" < exp_var "uv2"
       then
         call write_reg (exp_var "lv") (exp_inl (exp_val ty_int 1%Z)) ;;
         use lemma int_safe [exp_val ty_int 1%Z]
       else
         call write_reg (exp_var "lv") (exp_inl (exp_val ty_int 0%Z)) ;;
         use lemma int_safe [exp_val ty_int 0%Z]) ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_perm_to_bits : Stm ["p" ∶ ty_perm] ty_int :=
      match: exp_var "p" in permission with
      | O => stm_val ty_int 0%Z
      | R => stm_val ty_int 1%Z
      | RW => stm_val ty_int 2%Z
      end.

    Definition fun_perm_from_bits : Stm ["i" ∶ ty_int] ty_perm :=
      if: exp_var "i" = (exp_val ty_int 1%Z)
      then stm_val ty_perm R
      else if: exp_var "i" = (exp_val ty_int 2%Z)
           then stm_val ty_perm RW
           else stm_val ty_perm O.

    Definition fun_is_sub_perm : Stm ["p" ∶ ty_perm, "p'" ∶ ty_perm] ty_bool :=
      match: exp_var "p" in permission with
      | O =>
        stm_val ty_bool true
      | R => match: exp_var "p'" in permission with
            | O => stm_val ty_bool false
            | _ =>
              stm_val ty_bool true
            end
      | RW => match: exp_var "p'" in permission with
             | RW =>
               stm_val ty_bool true
            | _ => stm_val ty_bool false
            end
      end.

    Definition fun_is_within_range : Stm ["b'" ∶ ty_addr, "e'" ∶ ty_addr,
                                          "b" ∶ ty_addr, "e" ∶ ty_addr] ty_bool :=
      (exp_var "b" <= exp_var "b'") && (exp_var "e'" <= exp_var "e").

    Definition fun_exec_subseg : Stm ["lv" ∶ ty_lv, "hv1" ∶ ty_hv, "hv2" ∶ ty_hv]
                                     ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv2") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv") in
      let: "new_begin" :: ty_int := call read_reg_num (exp_var "hv1") in
      let: "new_end" :: ty_int := call read_reg_num (exp_var "hv2") in
      let*: ["perm", "begin", "end", "cursor"] := (exp_var "c") in
      (let: "b" :: ty_bool := call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                   (exp_var "begin") (exp_var "end") in
       stm_assert (exp_var "b") (exp_string "Err: [subseg] tried to increase range of authority") ;;
       let: "c'" :: cap := exp_record capability
                                      [ exp_var "perm",
                                        exp_var "new_begin",
                                        exp_var "new_end",
                                        exp_var "cursor"
                                      ] in
       use lemma gen_dummy [exp_var "c'"] ;;
       use lemma safe_within_range [exp_var "c'", exp_var "c"] ;;
       call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_subsegi : Stm ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int]
                                      ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv") in
      let: "new_begin" :: ty_int := call read_reg_num (exp_var "hv") in
      let: "new_end" :: ty_int := exp_var "immediate" in
      let*: ["perm", "begin", "end", "cursor"] := (exp_var "c") in
      (let: "b" :: ty_bool := call is_within_range (exp_var "new_begin") (exp_var "new_end")
                                   (exp_var "begin") (exp_var "end") in
       stm_assert (exp_var "b") (exp_string "Err: [subsegi] tried to increase range of authority") ;;
       let: "c'" :: cap := exp_record capability
                                      [ exp_var "perm",
                                        exp_var "new_begin",
                                        exp_var "new_end",
                                        exp_var "cursor"
                                      ] in
       use lemma gen_dummy [exp_var "c'"] ;;
       use lemma safe_within_range [exp_var "c'", exp_var "c"] ;;
       call write_reg (exp_var "lv") (exp_inr (exp_var "c'")) ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_isptr : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      let: w :: ty_word := call read_reg (exp_var "lv2") in
      match: w with
      | inl i =>
        use lemma int_safe [exp_val ty_int 0%Z] ;;
        call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 0%Z))
      | inr c =>
        use lemma int_safe [exp_val ty_int 1%Z] ;;
        call write_reg (exp_var "lv1") (exp_inl (exp_val ty_int 1%Z))
      end ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_getp : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: "i" :: ty_int := call perm_to_bits (exp_var "perm") in
       call write_reg (exp_var "lv1") (exp_inl (exp_var "i")) ;;
       use lemma int_safe [exp_var "i"] ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_getb : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (call write_reg (exp_var "lv1") (exp_inl (exp_var "beg")) ;;
       use lemma int_safe [exp_var "beg"] ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_gete : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (call write_reg (exp_var "lv1") (exp_inl (exp_var "end")) ;;
       use lemma int_safe [exp_var "end"] ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_geta : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv2") (fun _ => stm_val ty_unit tt) ;;
      let: c :: cap := call read_reg_cap (exp_var "lv2") in
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (call write_reg (exp_var "lv1") (exp_inl (exp_var "cursor")) ;;
       use lemma int_safe [exp_var "cursor"] ;;
       call update_pc ;;
       stm_val ty_bool true).

    Definition fun_exec_fail : Stm ε ty_bool :=
      fail "machine failed".

    Definition fun_exec_ret : Stm ε ty_bool :=
      stm_exp exp_false.

    Definition fun_exec_mv : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_bool :=
      stm_match_enum regname (exp_var "hv") (fun _ => stm_val ty_unit tt) ;;
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      let: w :: word := call read_reg (exp_var hv) in
      call write_reg lv (exp_var w) ;;
      call update_pc ;;
      stm_val ty_bool true.

    Definition fun_exec_jr : Stm ["lv" ∶ ty_lv] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      let: "c" :: ty_cap := call read_reg_cap (exp_var "lv") in
      stm_write_register pc (exp_var "c") ;;
      stm_val ty_bool true.

    Definition fun_exec_jalr : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      use lemma safe_move_cursor [exp_var "npc", exp_var "opc"] ;;
      stm_match_enum regname (exp_var "lv1") (fun _ => stm_val ty_unit tt) ;;
      call write_reg (exp_var "lv1") (exp_inr (exp_var "npc")) ;;
      call exec_jr (exp_var "lv2").

    Definition fun_exec_j : Stm [offset ∶ ty_int ] ty_bool :=
      call add_pc (exp_binop binop_times (exp_var offset) (exp_int 2)) ;;
      stm_val ty_bool true.

    Definition fun_exec_jal : Stm [lv ∶ ty_lv, offset ∶ ty_int] ty_bool :=
      let: "opc" := stm_read_register pc in
      let: "npc" := call next_pc in
      use lemma safe_move_cursor [exp_var "npc", exp_var "opc"] ;;
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      call write_reg lv (exp_inr (exp_var "npc")) ;;
      call exec_j offset.

    Definition fun_exec_bnez : Stm ["lv" ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      stm_match_enum regname (exp_var "lv") (fun _ => stm_val ty_unit tt) ;;
      let: "c" :: ty_int := call read_reg_num (exp_var "lv") in
      stm_if (exp_binop binop_eq (exp_var "c") (exp_int 0))
             (call update_pc ;; stm_val ty_bool true)
             (call add_pc (exp_var "immediate") ;; stm_val ty_bool true).

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjr        => MkAlt (pat_var lv) (call exec_jr lv)
           | kjalr      => MkAlt (pat_pair "lv1" "lv2") (call exec_jalr (exp_var "lv1") (exp_var "lv2"))
           | kj         => MkAlt (pat_var offset) (call exec_j offset)
           | kjal       => MkAlt (pat_pair lv offset) (call exec_jal lv offset)
           | kbnez      => MkAlt (pat_pair lv immediate) (call exec_bnez lv immediate)
           | kmv        => MkAlt (pat_pair lv hv) (call exec_mv lv hv)
           | kld        => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_ld (exp_var lv) (exp_var hv) (exp_var immediate))
           | ksd        => MkAlt (pat_tuple [hv , lv , immediate])
                            (call exec_sd (exp_var hv) (exp_var lv) (exp_var immediate))
           | klea       => MkAlt (pat_pair lv hv) (call exec_lea lv hv)
           | krestrict  => MkAlt (pat_pair lv hv) (call exec_restrict lv hv)
           | krestricti => MkAlt (pat_pair lv immediate) (call exec_restricti lv immediate)
           | ksubseg    => MkAlt (pat_tuple [lv , "hv1" , "hv2"])
                            (call exec_subseg (exp_var lv) (exp_var "hv1") (exp_var "hv2"))
           | ksubsegi   => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_subsegi (exp_var lv) (exp_var hv) (exp_var immediate))
           | kaddi      => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_addi (exp_var lv) (exp_var hv) (exp_var immediate))
           | kadd       => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_add (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | ksub       => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_sub (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kslt       => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_slt (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kslti      => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_slti (exp_var lv) (exp_var hv) (exp_var immediate))
           | ksltu      => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_sltu (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | ksltiu     => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_sltiu (exp_var lv) (exp_var hv) (exp_var immediate))
           | kisptr     => MkAlt (pat_pair "lv1" "lv2") (call exec_isptr (exp_var "lv1") (exp_var "lv2"))
           | kgetp      => MkAlt (pat_pair "lv1" "lv2") (call exec_getp (exp_var "lv1") (exp_var "lv2"))
           | kgetb      => MkAlt (pat_pair "lv1" "lv2") (call exec_getb (exp_var "lv1") (exp_var "lv2"))
           | kgete      => MkAlt (pat_pair "lv1" "lv2") (call exec_gete (exp_var "lv1") (exp_var "lv2"))
           | kgeta      => MkAlt (pat_pair "lv1" "lv2") (call exec_geta (exp_var "lv1") (exp_var "lv2"))
           | kfail      => MkAlt pat_unit (call exec_fail)
           | kret       => MkAlt pat_unit (call exec_ret)
           end).

    Definition fun_read_mem : Stm ["c" ∶ ty_cap] ty_memval :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: p :: bool := call read_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [read_mem] no read permission") ;;
       let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [read_mem] out of bounds") ;;
       foreign rM (exp_var "cursor")).

    Definition fun_write_mem : Stm ["c" ∶ ty_cap, "v" ∶ ty_memval ] ty_unit :=
      let*: ["perm", "beg", "end", "cursor"] := (exp_var "c") in
      (let: p :: bool := call write_allowed (exp_var "perm") in
       stm_assert p (exp_string "Err: [write_mem] no read permission") ;;
       let: q :: bool := call within_bounds c in
       stm_assert q (exp_string "Err: [write_mem] out of bounds") ;;
       foreign wM (exp_var "cursor") (exp_var "v")).

    Definition fun_exec : Stm ε ty_bool :=
      let: "c" := stm_read_register pc in
      let: n :: ty_memval := call read_mem c in
      match: (exp_var "n") with
      | inl n => 
        let: i :: ty_instr := foreign dI (exp_var n) in
        call exec_instr i
      | inr c => fail "Err [exec]: instructions cannot be capabilities"
      end.

    Definition fun_loop : Stm ε ty_unit :=
      let: "r" := call exec in
      if: exp_var "r"
      then call loop
      else stm_val ty_unit tt.

  End ExecStore.

  Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg        => fun_read_reg
    | read_reg_cap    => fun_read_reg_cap
    | read_reg_num    => fun_read_reg_num
    | write_reg       => fun_write_reg
    | next_pc         => fun_next_pc
    | update_pc       => fun_update_pc
    | add_pc          => fun_add_pc
    | read_mem        => fun_read_mem
    | write_mem       => fun_write_mem
    | read_allowed    => fun_read_allowed
    | write_allowed   => fun_write_allowed
    | upper_bound     => fun_upper_bound
    | within_bounds   => fun_within_bounds
    | perm_to_bits    => fun_perm_to_bits
    | perm_from_bits  => fun_perm_from_bits
    | is_sub_perm     => fun_is_sub_perm
    | is_within_range => fun_is_within_range
    | abs             => fun_abs
    | exec_jr         => fun_exec_jr
    | exec_jalr       => fun_exec_jalr
    | exec_j          => fun_exec_j
    | exec_jal        => fun_exec_jal
    | exec_bnez       => fun_exec_bnez
    | exec_mv         => fun_exec_mv
    | exec_ld         => fun_exec_ld
    | exec_sd         => fun_exec_sd
    | exec_lea        => fun_exec_lea
    | exec_restrict   => fun_exec_restrict
    | exec_restricti  => fun_exec_restricti
    | exec_subseg     => fun_exec_subseg
    | exec_subsegi    => fun_exec_subsegi
    | exec_addi       => fun_exec_addi
    | exec_add        => fun_exec_add
    | exec_sub        => fun_exec_sub
    | exec_slt        => fun_exec_slt
    | exec_slti       => fun_exec_slti
    | exec_sltu       => fun_exec_sltu
    | exec_sltiu      => fun_exec_sltiu
    | exec_isptr      => fun_exec_isptr
    | exec_getp       => fun_exec_getp
    | exec_getb       => fun_exec_getb
    | exec_gete       => fun_exec_gete
    | exec_geta       => fun_exec_geta
    | exec_fail       => fun_exec_fail
    | exec_ret        => fun_exec_ret
    | exec_instr      => fun_exec_instr
    | exec            => fun_exec
    | loop            => fun_loop
    end.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* MEMORY *)
  Definition Memory := Addr -> (Z + Capability).

  Definition fun_rM (μ : Memory) (addr : Val ty_int) : Val ty_memval :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr : Val ty_int) (val : Val ty_memval) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
    forall (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
    match f with
    | rM      => fun args res γ γ' μ μ' =>
                   let addr := (args ‼ "address")%exp in
                   (γ' , μ' , res) = (γ , μ , inr (fun_rM μ addr))
    | wM      => fun args res γ γ' μ μ' =>
                   let addr := (args ‼ "address")%exp in
                   let val  := (args ‼ "new_value")%exp in
                   (γ' , μ' , res) = (γ , fun_wM μ addr val , inr tt)
    | dI      => fun args res γ γ' μ μ' =>
                   let code := (args ‼ "code")%exp in
                   (* Non-deterministically return any possible result *)
                   (exists res' : Val (ty_sum ty_string ty_instr),
                     (γ' , μ' , res) = (γ , μ , res'))%type
    end.

  Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
    exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args. exists γ, μ, (inr ret), (inr ret). reflexivity.
  Qed.

End MinCapsProgramKit.
