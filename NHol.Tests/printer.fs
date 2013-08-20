(*

Copyright 2013 Jack Pappas, Anh-Dung Phan, Eric Taucher

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

/// Tests for functions in the NHol.printer module.
module Tests.NHol.printer

open NUnit.Framework

(* OCaml.Compatability. *)
(* isspace  tests *)
(* issep  tests *)
(* isbra  tests *)
(* issymb  tests *)
(* isalpha  tests *)
(* isnum  tests *)
(* isalnum  tests *)
(* reserve_words  tests *)
(* unreserve_words  tests *)
(* is_reserved_word  tests *)
(* reserved_words  tests *)
(* unparse_as_binder  tests *)
(* parse_as_binder  tests *)
(* parses_as_binder  tests *)
(* binders  tests *)
(* unparse_as_prefix  tests *)
(* parse_as_prefix  tests *)
(* is_prefix  tests *)
(* prefixes  tests *)
(* unparse_as_infix  tests *)
(* parse_as_infix  tests *)
(* get_infix_status  tests *)
(* infixes  tests *)
(* open_box  tests *)
(* close_box  tests *)
(* print_string  tests *)
(* print_as  tests *)
(* print_int  tests *)
(* print_float  tests *)
(* print_char  tests *)
(* print_bool  tests *)
(* print_space  tests *)
(* print_cut  tests *)
(* print_break  tests *)
(* print_flush  tests *)
(* print_newline  tests *)
(* force_newline  tests *)
(* print_if_newline  tests *)
(* set_margin  tests *)
(* get_margin  tests *)
(* set_max_indent  tests *)
(* get_max_indent  tests *)
(* set_max_boxes  tests *)
(* get_max_boxes  tests *)
(* over_max_boxes  tests *)
(* open_hbox  tests *)
(* open_vbox  tests *)
(* xyzopen_hvbox  tests *)
(* open_hovbox  tests *)
(* open_tbox  tests *)
(* close_tbox  tests *)
(* print_tbreak   tests *)
(* set_tab  tests *)
(* print_tab  tests *)
(* set_ellipsis_text  tests *)
(* get_ellipsis_text  tests *)
(* open_tag  tests *)
(* close_tag  tests *)
(* set_tags  tests *)
(* set_print_tags  tests *)
(* set_mark_tags  tests *)
(* get_print_tags  tests *)
(* get_mark_tags  tests *)
(* set_formatter_out_channel  tests *)
(* set_formatter_output_functions  tests *)
(* get_formatter_output_functions  tests *)
(* set_all_formatter_output_functions  tests *)
(* get_all_formatter_output_functions  tests *)
(* set_formatter_tag_functions  tests *)
(* get_formatter_tag_functions  tests *)
(* formatter_of_out_channel  tests *)
(* std_formatter  tests *)
(* err_formatter  tests *)
(* formatter_of_buffer  tests *)
(* stdbuf  tests *)
(* str_formatter  tests *)
(* flush_str_formatter  tests *)
(* make_formatter  tests *)
(* pp_open_hbox  tests *)
(* pp_open_vbox  tests *)
(* pp_open_hvbox  tests *)
(* pp_open_hovbox  tests *)
(* pp_open_box  tests *)
(* pp_close_box  tests *)
(* pp_open_tag  tests *)
(* pp_close_tag  tests *)
(* pp_print_string  tests *)
(* pp_print_as  tests *)
(* pp_print_int  tests *)
(* pp_print_float  tests *)
(* pp_print_char  tests *)
(* pp_print_bool  tests *)
(* pp_print_break  tests *)
(* pp_print_cut  tests *)
(* pp_print_space  tests *)
(* pp_force_newline  tests *)
(* pp_print_flush  tests *)
(* pp_print_newline  tests *)
(* pp_print_if_newline  tests *)
(* pp_open_tbox  tests *)
(* pp_close_tbox  tests *)
(* pp_print_tbreak  tests *)
(* pp_set_tab  tests *)
(* pp_print_tab  tests *)
(* pp_set_tags  tests *)
(* pp_set_print_tags  tests *)
(* pp_set_mark_tags  tests *)
(* pp_get_print_tags  tests *)
(* pp_get_mark_tags  tests *)
(* pp_set_margin  tests *)
(* pp_get_margin  tests *)
(* pp_set_max_indent  tests *)
(* pp_get_max_indent  tests *)
(* pp_set_max_boxes  tests *)
(* pp_get_max_boxes  tests *)
(* pp_over_max_boxes  tests *)
(* pp_set_ellipsis_text  tests *)
(* pp_get_ellipsis_text  tests *)
(* pp_set_formatter_out_channel  tests *)
(* pp_set_formatter_output_functions  tests *)
(* pp_get_formatter_output_functions  tests *)
(* pp_set_all_formatter_output_functions  tests *)
(* pp_get_all_formatter_output_functions  tests *)
(* pp_set_formatter_tag_functions  tests *)
(* pp_get_formatter_tag_functions  tests *)
(* fprintf  tests *)
(* printf  tests *)
(* eprintf  tests *)
(* sprintf  tests *)
(* bprintf  tests *)
(* kfprintf  tests *)
(* ifprintf  tests *)
(* ksprintf  tests *)
(* kprintf  tests *)

(* charcode  tests *)

(* ctable  tests *)

(* checkStringIsSingleChar  tests *)

(* name_of  tests *)

(* pp_print_type  tests *)

(* pp_print_qtype  tests *)

(* install_user_printer  tests *)

(* delete_user_printer  tests *)

(* try_user_printer  tests *)

(* pp_print_term  tests *)

(* pp_print_qterm  tests *)

(* pp_print_thm  tests *)

(* print_type  tests *)

(* print_qtype  tests *)

(* print_term  tests *)

(* print_qterm  tests *)

(* print_thm  tests *)

(* print_to_string  tests *)

(* string_of_type  tests *)

(* string_of_term  tests *)

(* string_of_thm  tests *)
