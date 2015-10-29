type esh = Defs.ext_symb_heap
val entails : esh -> esh -> bool

type frame = esh option
val get_frame : esh -> esh -> esh option
