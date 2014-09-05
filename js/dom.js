function unwrapDOMObject(obj) {
  if (obj.hasOwnProperty("_wrappedDOMObject")) {
    return obj._wrappedDOMObject;
  }

  return obj;
}

function wrapDOMFunction(obj, fn) {
    return function(argcv) {
        var args = Array.prototype.slice.call(arguments, 1);
        for (var i=0; i<args.length; i++)
            args[i] = wrapGraceObject(args[i]);
        return wrapDOMObject(obj[fn].apply(obj, args));
    }
}

function wrapDOMField(o, obj, k) {
    o.methods[k + ":="] = function(argcv, val) {
        obj[k] = wrapGraceObject(val);
        return var_done;
    }
    return function() {
        return wrapDOMObject(obj[k]);
    }
}
function wrapDOMObject(obj) {
    switch(typeof obj) {
        case "boolean":
            return new GraceBoolean(obj);
        case "string":
            return new GraceString(obj);
        case "number":
            return new GraceNum(obj);
        case "undefined":
            return var_done;
    }
    if (obj == null) {
      return var_done;
    }
    if (obj._graceWrapper)
        return obj._graceWrapper;
    var o = Grace_allocObject();
    o._wrappedDOMObject = obj;
    o.methods.asString = function() {
        return new GraceString("DOMObject(" + obj + ")");
    }
    for (var k in obj) {
        switch(typeof obj[k]) {
            case "function":
                o.methods[k] = wrapDOMFunction(obj, k);
                break;
            case "string":
            case "boolean":
            case "number":
            case "object":
                o.methods[k] = wrapDOMField(o, obj, k);
                break
        }
    }
    o.methods._methods = function() {
        var l = [];
        for (var m in o.methods) {
            l.push(new GraceString(m));
        }
        return new GraceList(l);
    }
    try {
        obj._graceWrapper = o;
    } catch(e) {}
    return o;
}

function wrapGraceObject(o) {
    if (o === undefined || o === null)
        return var_done;
    if (o instanceof GraceString) {
        return o._value;
    }
    if (o instanceof GraceNum) {
        return o._value;
    }
    if (o instanceof GraceBoolean) {
        return o._value;
    }
    if (o.real) { // A block
        if (o._wrappedDOMObject)
            return o._wrappedDOMObject;
        var f = function() {
            var args = [];
            for (var i=0; i<arguments.length; i++) {
                args.push(wrapDOMObject(arguments[i]));
            }
            var ret
            minigrace.trapErrors(function() {
                ret = wrapGraceObject(o.real.apply(o.receiver, args));
            });
            return ret
        }
        o._wrappedDOMObject = f;
    }
    if (o._wrappedDOMObject)
        return o._wrappedDOMObject;
    return o;
}

function gracecode_dom() {
    this.methods.document = function(argcv) {
        return wrapDOMObject(document);
    };
    this.methods.document.paramCounts = [0];
    this.methods.document.variableArities = [false];

    this.methods.window = function(argcv) {
        var win = wrapDOMObject(window);
        win.methods["Math"] = function() {
            return {"methods": {
                "cos": wrapDOMFunction(Math, "cos"),
                "sin": wrapDOMFunction(Math, "sin"),
                "tan": wrapDOMFunction(Math, "tan"),
                "asin": wrapDOMFunction(Math, "asin"),
                "acos": wrapDOMFunction(Math, "acos"),
                "atan": wrapDOMFunction(Math, "atan"),
                "atan2": wrapDOMFunction(Math, "atan2"),
            }}
        };
        return win;
    };

    this.methods.window.paramCounts = [0];
    this.methods.window.variableArities = [false];

    this.methods["doesObject()haveProperty"] = function (argcv, object, name) {
        return name._value in unwrapDOMObject(object) ? GraceTrue : GraceFalse;
    };

    this.methods["for()waiting()do"] = function(argcv, iterable, delay, block) {
        var ret = Grace_allocObject();
        ret.methods.then = function(argcv, block) {
            this.data["then"] = block;
        }
        var iter = callmethod(iterable, "iterator", [0]);
        var func = function() {
            minigrace.trapErrors(function() {
                if (Grace_isTrue(callmethod(iter, "havemore", [0]))) {
                    var val = callmethod(iter, "next", [0]);
                    callmethod(block, "apply", [1], val);
                    setTimeout(func, delay._value);
                } else {
                    if (ret.data.then)
                        callmethod(ret.data.then, "apply", [0]);
                }
            });
        }
        func();
        return ret;
    };
    this.methods["for()waiting()do"].paramCounts = [1, 1, 1];
    this.methods["for()waiting()do"].variableArities = [false, false, false];

    this.methods["while()waiting()do"] = function(argcv, cond, delay, block) {
        var ret = Grace_allocObject();
        ret.methods.then = function(argcv, block) {
            this.data["then"] = block;
        }
        var func = function() {
            minigrace.trapErrors(function() {
                if (Grace_isTrue(callmethod(cond, "apply", [0]))) {
                    callmethod(block, "apply", [0]);
                    setTimeout(func, delay._value);
                } else {
                    if (ret.data.then)
                        callmethod(ret.data.then, "apply", [0]);
                }
            });
        }
        func();
        return ret;
    };
    this.methods["while()waiting()do"].paramCounts = [1, 1, 1];
    this.methods["while()waiting()do"].variableArities = [false, false, false];
    return this;
}

gracecode_dom.imports = [
];
if (typeof gctCache !== "undefined")
gctCache['dom'] = "modules:\nfresh-methods:\npath:\n dom\nclasses:\npublic:\n document\n window\n for()waiting()do\n while()waiting()do\nconfidential:\n";
