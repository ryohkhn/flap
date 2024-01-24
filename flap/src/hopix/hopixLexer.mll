{ (* -*- tuareg -*- *)
  open Lexing
  open Error
  open Position
  open HopixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)


}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let comment_start = "{*"

let comment_end = "*}"

let digit = ['0'-'9']

let var_id = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let constr_id = ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let label_id = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let type_con = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let type_variable = '`' ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let int = '-'? ['0'-'9']+ | "0x" ['0'-'9' 'a'-'f' 'A'-'F']+ | "0b" ['0'-'1'] | "0o" ['0'-'7']+

let printable = [' '-'~'] # '\''

let atom = ['\x00'-'\xFF'] | '\\' '0' 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] | printable | '\\' | '\'' | '\n' | '\t' | '\b' | '\r'

let char = '\'' atom '\''

let string = '\"' (atom | '\'' | '\\' '\"' # '\"')* '\"'

rule comment depth = parse
  | comment_start
      { comment (depth + 1) lexbuf }
  | comment_end
      { if depth > 1 then comment (depth - 1) lexbuf else () }
  | eof
      { error lexbuf "Unexpected end of file inside a comment" }
  | _
      { comment depth lexbuf }

and token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf }
  | "##" newline    { next_line_and token lexbuf }
  | comment_start   { comment 1 lexbuf; token lexbuf }
  
  (** KeyWords *)
  |"if"       { IF }
  |"do"       { DO }
  |"to"       { TO }
  |"let"      { LET }
  |"fun"      { FUN }
  |"and"      { AND }
  |"ref"      { REF }
  |"for"      { FOR }
  |"type"     { TYPE }
  |"then"     { THEN }
  |"else"     { ELSE }
  |"from"     { FROM }
  |"match"    { MATCH }
  |"until"    { UNTIL }
  |"extern"   { EXTERN }
  |"while"    { WHILE }

  (** Symbols *)
  | var_id as v | label_id as v | type_con as v       { COMMON_ID v }
  | constr_id as c                                    { CONSTR_ID c }
  | type_variable as t                                { TYPE_VAR t }
  | int as i                                          { INT i }
  | char as c                                         { CHAR (char_of_int (int_of_string c)) }
  | string as s                                       { STRING s }

  (** BinOp *)
  |"="        { EQUAL }
  |"+"        { PLUS }
  |"-"        { DASH }
  |"*"        { STAR }
  |"/"        { SLASH }
  |"\\"	      { ANTISLASH }
  |"&&"       { LAND }
  |"||"       { LOR }
  |"->"       { ARROW }
  |"=?"       { EQ }
  |"<=?"      { LOE }
  |">=?"      { HOE }
  |"<?"       { INFT }
  |">?"       { SUPT }
  | ">"       { RANGLE }
  | "<"       { LANGLE }

  (** Ponctuation *)
  |"."        { POINT }
  |"_"        { WILDCARD }
  |";"        { SEMICOLON }
  |":"        { COLON }
  |"<"        { LANGLE }
  |">"        { RANGLE }
  |"("        { PO }
  |")"        { PF }
  |"["        { CO }
  |"]"        { CF }
  |"{"        { AO }
  |"}"        { AF }
  |"|"        { PIPE }
  |"!"        { MARK }
  |","        { COMMA }
  |"&"        { ECOM }
  |":="       { DEQUAL }
  | eof       { EOF }
  
  
  (** Lexing error. *)
  | _        { error lexbuf "unexpected character." }
