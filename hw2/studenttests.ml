open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)


let provided_tests : suite = [
  Test ("separate_segments", [
    ("separate_segments_1", assert_eqf (fun () -> separate_segments []) ([], []));
    ("separate_segments_2", assert_eqf (fun () -> separate_segments [text "foo" []]) ([text "foo" []], []));
    ("separate_segments_3", assert_eqf (fun () -> separate_segments [text "foo" []; text "bar" []]) ([text "foo" []; text "bar" []], []));
    ("separate_segments_4", assert_eqf (fun () -> separate_segments [text "foo" []; data "xyz" [Quad (Lit 42L)]; gtext "bar" []; data "uvw" []]) ([text "foo" []; gtext "bar" []], [data "xyz" [Quad (Lit 42L)]; data "uvw" []]));
  ]);

  Test ("calc_label_addresses", [
    ("calc_label_addresses_1", assert_eqf (fun () -> calc_label_addresses 0L []) []);
    ("calc_label_addresses_2", assert_eqf (fun () -> calc_label_addresses 0L [text "foo" []]) [(Lbl "foo", Lit 0L)]);
    ("calc_label_addresses_3", assert_eqf (fun () -> calc_label_addresses 100L [text "foo" [Retq, []]; text "bar" []]) [(Lbl "foo", Lit 100L); (Lbl "bar", Lit 108L)]);
    ("calc_label_addresses_4", assert_eqf (fun () -> calc_label_addresses 100L [text "foo" [Retq, []]; text "bar" []; data "xyz" [Quad (Lit 42L)]]) [(Lbl "foo", Lit 100L); (Lbl "bar", Lit 108L); (Lbl "xyz", Lit 108L)]);
    ("calc_label_addresses_5", assert_eqf (fun () -> calc_label_addresses 0x400000L Gradedtests.helloworld) [(Lbl "foo", Lit 0x400000L); (Lbl "main", Lit 0x400018L); (Lbl "baz", Lit 0x400030L)]);
    ("calc_label_addresses_6", (fun () -> try ignore (calc_label_addresses 0L [text "foo" []; data "foo" []]); failwith "expecting Redefined_sym" with (Redefined_sym "foo") -> ()));
  ]);

] 
