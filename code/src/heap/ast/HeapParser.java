
//----------------------------------------------------
// The following code was generated by CUP v0.10k
// Mon Dec 11 20:44:19 IST 2017
//----------------------------------------------------

package heap.ast;

import java.io.*;
import java.util.*;
import heap.ast.Token;

/** CUP v0.10k generated parser.
  * @version Mon Dec 11 20:44:19 IST 2017
  */
@SuppressWarnings({"rawtypes", "unused"}) public class HeapParser extends java_cup.runtime.lr_parser {

  /** Default constructor. */
  public HeapParser() {super();}

  /** Constructor which sets the default scanner. */
  public HeapParser(java_cup.runtime.Scanner s) {super(s);}

  /** Production table. */
  protected static final short _production_table[][] = 
    unpackFromStrings(new String[] {
    "\000\034\000\002\003\003\000\002\002\004\000\002\004" +
    "\003\000\002\004\004\000\002\005\003\000\002\005\003" +
    "\000\002\005\003\000\002\006\007\000\002\007\003\000" +
    "\002\007\004\000\002\010\005\000\002\010\005\000\002" +
    "\011\015\000\002\012\003\000\002\012\005\000\002\013" +
    "\005\000\002\014\003\000\002\014\005\000\002\015\004" +
    "\000\002\016\012\000\002\017\003\000\002\020\003\000" +
    "\002\020\004\000\002\021\003\000\002\022\006\000\002" +
    "\022\010\000\002\022\010\000\002\022\010" });

  /** Access to production table. */
  public short[][] production_table() {return _production_table;}

  /** Parse-action table. */
  protected static final short[][] _action_table = 
    unpackFromStrings(new String[] {
    "\000\100\000\006\004\013\020\005\001\002\000\010\002" +
    "\001\004\013\020\005\001\002\000\006\014\030\016\027" +
    "\001\002\000\010\002\ufffc\004\ufffc\020\ufffc\001\002\000" +
    "\010\002\ufffb\004\ufffb\020\ufffb\001\002\000\004\002\026" +
    "\001\002\000\010\002\uffff\004\uffff\020\uffff\001\002\000" +
    "\010\002\ufffd\004\ufffd\020\ufffd\001\002\000\004\020\014" +
    "\001\002\000\004\016\015\001\002\000\004\020\016\001" +
    "\002\000\004\012\023\001\002\000\006\017\021\020\016" +
    "\001\002\000\006\017\ufff9\020\ufff9\001\002\000\010\002" +
    "\ufffa\004\ufffa\020\ufffa\001\002\000\006\017\ufff8\020\ufff8" +
    "\001\002\000\006\006\025\020\024\001\002\000\006\017" +
    "\ufff7\020\ufff7\001\002\000\006\017\ufff6\020\ufff6\001\002" +
    "\000\004\002\000\001\002\000\004\017\055\001\002\000" +
    "\004\020\031\001\002\000\004\012\053\001\002\000\006" +
    "\011\ufff4\015\ufff4\001\002\000\006\011\034\015\035\001" +
    "\002\000\004\020\031\001\002\000\004\013\036\001\002" +
    "\000\004\014\037\001\002\000\004\020\031\001\002\000" +
    "\006\011\034\015\041\001\002\000\004\016\042\001\002" +
    "\000\004\005\043\001\002\000\004\020\051\001\002\000" +
    "\006\011\ufff1\017\ufff1\001\002\000\006\011\046\017\047" +
    "\001\002\000\004\005\043\001\002\000\010\002\ufff5\004" +
    "\ufff5\020\ufff5\001\002\000\006\011\ufff0\017\ufff0\001\002" +
    "\000\006\011\uffef\017\uffef\001\002\000\006\011\ufff3\015" +
    "\ufff3\001\002\000\004\020\054\001\002\000\006\011\ufff2" +
    "\015\ufff2\001\002\000\004\020\056\001\002\000\004\014" +
    "\070\001\002\000\010\013\uffec\017\uffec\020\uffec\001\002" +
    "\000\004\013\064\001\002\000\010\013\uffea\017\uffea\020" +
    "\uffea\001\002\000\010\013\uffed\017\uffed\020\056\001\002" +
    "\000\010\013\uffeb\017\uffeb\020\uffeb\001\002\000\004\016" +
    "\065\001\002\000\004\020\056\001\002\000\004\017\067" +
    "\001\002\000\010\002\uffee\004\uffee\020\uffee\001\002\000" +
    "\004\020\071\001\002\000\006\011\072\015\073\001\002" +
    "\000\010\007\076\010\075\020\074\001\002\000\010\013" +
    "\uffe9\017\uffe9\020\uffe9\001\002\000\004\015\101\001\002" +
    "\000\004\015\100\001\002\000\004\015\077\001\002\000" +
    "\010\013\uffe7\017\uffe7\020\uffe7\001\002\000\010\013\uffe6" +
    "\017\uffe6\020\uffe6\001\002\000\010\013\uffe8\017\uffe8\020" +
    "\uffe8\001\002\000\010\002\ufffe\004\ufffe\020\ufffe\001\002" +
    "" });

  /** Access to parse-action table. */
  public short[][] action_table() {return _action_table;}

  /** <code>reduce_goto</code> table. */
  protected static final short[][] _reduce_table = 
    unpackFromStrings(new String[] {
    "\000\100\000\016\003\007\004\003\005\010\006\011\011" +
    "\005\016\006\001\001\000\012\005\101\006\011\011\005" +
    "\016\006\001\001\000\002\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\002\001\001\000\006\007" +
    "\016\010\017\001\001\000\002\001\001\000\004\010\021" +
    "\001\001\000\002\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\002\001\001\000\006\012\032\013" +
    "\031\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\004\013\051\001\001\000\002\001\001\000" +
    "\002\001\001\000\006\012\037\013\031\001\001\000\002" +
    "\001\001\000\002\001\001\000\006\014\044\015\043\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\004\015\047\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\012\017\057\020\061\021\056\022" +
    "\060\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\006\021\062\022\060\001" +
    "\001\000\002\001\001\000\002\001\001\000\012\017\065" +
    "\020\061\021\056\022\060\001\001\000\002\001\001\000" +
    "\002\001\001\000\002\001\001\000\002\001\001\000\002" +
    "\001\001\000\002\001\001\000\002\001\001\000\002\001" +
    "\001\000\002\001\001\000\002\001\001\000\002\001\001" +
    "\000\002\001\001\000\002\001\001" });

  /** Access to <code>reduce_goto</code> table. */
  public short[][] reduce_table() {return _reduce_table;}

  /** Instance of action encapsulation class. */
  protected CUP$HeapParser$actions action_obj;

  /** Action encapsulation object initializer. */
  protected void init_actions()
    {
      action_obj = new CUP$HeapParser$actions(this);
    }

  /** Invoke a user supplied parse action. */
  public java_cup.runtime.Symbol do_action(
    int                        act_num,
    java_cup.runtime.lr_parser parser,
    java.util.Stack            stack,
    int                        top)
    throws java.lang.Exception
  {
    /* call code in generated class */
    return action_obj.CUP$HeapParser$do_action(act_num, parser, stack, top);
  }

  /** Indicates start state. */
  public int start_state() {return 0;}
  /** Indicates start production. */
  public int start_production() {return 1;}

  /** <code>EOF</code> Symbol index. */
  public int EOF_sym() {return 0;}

  /** <code>error</code> Symbol index. */
  public int error_sym() {return 1;}



   private HeapLexer lexer;
    
   /** 
    */
   public void parseFile(String file) throws SyntaxError, FileNotFoundException, Exception {
	lexer = new HeapLexer(new FileReader(file));
	HeapParser parser = new HeapParser(lexer);
			
	try { 
		parser.parse();
	}
	finally {
		lexer = null;
	}
  }
  	
  @Override	
  public void report_fatal_error(String message, Object info) throws SyntaxError {
    Token token = (Token) info;
    throw new SyntaxError("Syntax error at " + token.line + ":" + token.column + " on " + token.text);
  }

}

/** Cup generated class to encapsulate user supplied action code.*/
@SuppressWarnings({"rawtypes", "unused"}) class CUP$HeapParser$actions {
  private final HeapParser parser;

  /** Constructor */
  CUP$HeapParser$actions(HeapParser parser) {
    this.parser = parser;
  }

  /** Method with the actual generated action code. */
  public final java_cup.runtime.Symbol CUP$HeapParser$do_action(
    int                        CUP$HeapParser$act_num,
    java_cup.runtime.lr_parser CUP$HeapParser$parser,
    java.util.Stack            CUP$HeapParser$stack,
    int                        CUP$HeapParser$top)
    throws java.lang.Exception
    {
      /* Symbol object for return from actions */
      java_cup.runtime.Symbol CUP$HeapParser$result;

      /* select the action based on the action number */
      switch (CUP$HeapParser$act_num)
        {
          /*. . . . . . . . . . . . . . . . . . . .*/
          case 27: // predVal ::= ID LP ID COMMA INT_VAL RP 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(16/*predVal*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-5)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 26: // predVal ::= ID LP ID COMMA NULL RP 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(16/*predVal*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-5)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 25: // predVal ::= ID LP ID COMMA ID RP 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(16/*predVal*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-5)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 24: // predVal ::= ID LP ID RP 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(16/*predVal*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-3)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 23: // heapElem ::= predVal 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(15/*heapElem*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 22: // heapElems ::= heapElems heapElem 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(14/*heapElems*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 21: // heapElems ::= heapElem 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(14/*heapElems*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 20: // symheap ::= heapElems 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(13/*symheap*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 19: // example ::= ID LCB RCB symheap ARROW LCB symheap RCB 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(12/*example*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-7)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 18: // temp ::= VAR ID 
            {
              Object RESULT = null;
		int IDleft = ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left;
		int IDright = ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right;
		String ID = (String)((java_cup.runtime.Symbol) CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).value;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(11/*temp*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 17: // temps ::= temps COMMA temp 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(10/*temps*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-2)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 16: // temps ::= temp 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(10/*temps*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 15: // arg ::= ID COLON ID 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(9/*arg*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-2)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 14: // args ::= args COMMA arg 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(8/*args*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-2)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 13: // args ::= arg 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(8/*args*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 12: // funDef ::= ID LP args RP ARROW LP args RP LCB temps RCB 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(7/*funDef*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-10)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 11: // field ::= ID COLON INT_TYPE 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(6/*field*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-2)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 10: // field ::= ID COLON ID 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(6/*field*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-2)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 9: // fields ::= fields field 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(5/*fields*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 8: // fields ::= field 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(5/*fields*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 7: // typeDef ::= TYPE ID LCB fields RCB 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(4/*typeDef*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-4)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 6: // elem ::= example 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(3/*elem*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 5: // elem ::= funDef 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(3/*elem*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 4: // elem ::= typeDef 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(3/*elem*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 3: // elemList ::= elemList elem 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(2/*elemList*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 2: // elemList ::= elem 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(2/*elemList*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 1: // $START ::= problem EOF 
            {
              Object RESULT = null;
		int start_valleft = ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left;
		int start_valright = ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).right;
		Object start_val = (Object)((java_cup.runtime.Symbol) CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).value;
		RESULT = start_val;
              CUP$HeapParser$result = new java_cup.runtime.Symbol(0/*$START*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-1)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          /* ACCEPT */
          CUP$HeapParser$parser.done_parsing();
          return CUP$HeapParser$result;

          /*. . . . . . . . . . . . . . . . . . . .*/
          case 0: // problem ::= elemList 
            {
              Object RESULT = null;

              CUP$HeapParser$result = new java_cup.runtime.Symbol(1/*problem*/, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).left, ((java_cup.runtime.Symbol)CUP$HeapParser$stack.elementAt(CUP$HeapParser$top-0)).right, RESULT);
            }
          return CUP$HeapParser$result;

          /* . . . . . .*/
          default:
            throw new Exception(
               "Invalid action number found in internal parse table");

        }
    }
}
