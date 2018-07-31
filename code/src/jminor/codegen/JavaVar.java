package jminor.codegen;

import jminor.BooleanType;
import jminor.IntType;
import jminor.RefVar;
import jminor.Var;

public final class JavaVar {
    public final String name;
    public final String defaultVal;
    public final String type;

    /*public String getType() {
        ST nonNullTypeST = templates.load("NonNullType");
        nonNullTypeST.add("type", this.type);
        return nonNullTypeST.render();
    }*/

    // TODO: clean this up - get the default value directly from the type.
    public JavaVar(Var v) {
        this.name = v.name;
        this.type = v.getType().getName();
        if (v.getType() instanceof IntType) {
            this.defaultVal = "0";
        } else if (v.getType() instanceof BooleanType) {
            this.defaultVal = "false";
        } else if (v instanceof RefVar) {
            this.defaultVal = "null";
        } else {
            throw new Error("Unsupported variable type: " + v);
        }
    }
}
