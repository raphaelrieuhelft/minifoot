let formatter = ref Format.std_formatter
let columns = ref 72

let print_gc_stats = false

let repetitions = ref 1

let verbose1 = ref false

(* default component tags *)
let list_data_tag = "hd"
let list_link_tag = "tl"
let tree_data_tag = "d"
let tree_link_tags = "l", "r"
let dl_Llink_tag,dl_Rlink_tag = tree_link_tags (* the parser assumes this *)

(* command line arguments *)
let speclist = (* Arg.align *)
  [("-repetitions", Arg.Int (fun n -> repetitions := n), "    Verify a number of times repeatedly");
   ("-columns", Arg.Int (fun n -> columns := n), "        Format output for a number of columns");
   ("-verbose", Arg.Unit (fun () -> verbose1 := true),"        Display additional internal information")]

let usage_msg =
  "Usage: " ^ Sys.argv.(0) ^
    " [-repetitions n] [-columns n] [-verbose] <files>"
