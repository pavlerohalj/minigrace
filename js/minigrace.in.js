// declare global variables used to monitor execution:
window.minigrace = {};
window.sourceObject = null;
window.invocationCount = 0;
window.onOuter = false;
window.onSelf = false;
window.gctCache = {};
window.originalSourceLines = {};
window.stackFrames = [];
window.Grace_prelude = {};

function MiniGrace() {
    this.compileError = false;
    this.vis = "standard";
    this.mode = "js";
    this.modname = "main";
    this.verbosity = 20;
    this.lastSourceCode = "";
    this.lastMode = "";
    this.lastModname = "";
    this.breakLoops = true;
    this.debugMode = false;
    this.lastDebugMode = false;
    this.printStackFrames = true;
    
    this.generated_output = "";
    
    this.stdout_write = function(value) {
        if(typeof(process) != "undefined") {
            process.stdout.write(value);
        }
    };
    
    this.stderr_write = function(value) {
        // This function is used only in the oldWeb interface.  The exp interface
        // replaces it with a different method in editor.js around line 138.
        // There, each error write is turned into an html div, and is thus a line
        // of its own.  For compatibility, we make each stderr_write a separate line.
        if(typeof(process) != "undefined") {
            process.stderr.write(value + "\n");
        } else {
            console.log(value + "\n");
        }
    };
    
    this.stdin_read = function() {
        if(typeof(process) != "undefined") {
            return process.stdin.read();
        } else {
            return "";
        }
    };
}

MiniGrace.prototype.compile = function(grace_code) {
    importedModules = {};
    do_import('standardGrace', gracecode_standardGrace);

    // Change stdin to read from code.
    var old_stdin_read = this.stdin_read;
    this.stdin_read = function() {
        return grace_code;
    };
    
    // Change stdout to store generated output.
    var old_stdout_write = this.stdout_write;
    this.stdout_write = function(value) {
        this.generated_output += value;
    };
    this.generated_output = "";
    
    this.compileError = false;
    extensionsMap = callmethod(var_HashMap, "new", [0]);
    if (this.vis !== "standard") {
        callmethod(extensionsMap, "put(2)", [2], new GraceString("DefaultVisibility"),
                   new GraceString(this.vis));
    }
    if (this.debugMode) {
        callmethod(extensionsMap, "put(2)", [2], new GraceString("Debug"), new GraceString("yes"));
    }
    try {
        gracecode_compiler.call(new GraceModule(":user:"));
    } catch (e) {
        if (e == "ErrorExit") {
            this.compileError = true;
            this.stderr_write("Compilation terminated.");
        } else if (e == "SystemExit") {
            // pass
        } else if (e.exctype == 'graceexception') {
            this.compileError = true;
            if (e.exception.name == 'ImportError') {
                this.stderr_write("Import error: " + e.message._value);
            } else if (e.exception.name == 'CheckerFailure') {
                this.stderr_write("Dialect detects an error: " + e.message._value);
            } else {
                var message;
                if (e.exception.name == 'DialectError') {
                    message = "Dialect " + e.message._value;
                } else {
                    message = "Internal compiler error at line " +
                    e.lineNumber + " of " + e.moduleName +
                    ". " + e.exception.name + ": " + e.message._value + "\n";
                }
                this.stderr_write(message);
                callmethod(e, "printBacktrace", [0]);
            }
            this.stderr_write("Compilation terminated.");
        } else {
            throw e;
        }
    } finally {
        // Change the stdin and stdout back.
        this.stdin_read = old_stdin_read;
        this.stdout_write = old_stdout_write;
    }
};

function padToFour(num) {
    return num <= 9999 ? ("   "+num).slice(-4) : num;
}

MiniGrace.prototype.trapErrors = function(func) {
    this.exception = null;
    try {
        func();
    } catch (e) {
        var eStr = e.toString();
        if ((eStr === "RangeError: Maximum call stack size exceeded") ||    // Chrome
            (eStr === "InternalError: too much recursion") ) {              // Firefox
            e = new GraceExceptionPacket(new GraceException("TooMuchRecursion", ProgrammingErrorObject),
                   new GraceString("does one of your methods request execution of itself without limit?"));
        }
        const stderr_write = this.stderr_write;
        if (e.exctype === "graceexception") {
            this.exception = e;
            if (e.exception.name === "AssertionFailure") {
                stderr_write("Assertion Failed: " + e.message._value);
                var skipable = new GraceList([
                            new GraceString("gUnit"),
                            new GraceString("minitest"),
                            new GraceString("minispec"),
                            new GraceString("beginningStudent")
                ]);
                callmethod(e, "printBacktraceSkippingModules", [1], skipable);
                // stderr_write("  requested on line " + lineNumber + " of " + this.lastModname + ".");
            } else {
                callmethod(e, "printBacktrace", [0]);
                // stderr_write("  requested on line " + lineNumber + " of " + this.lastModname + ".\n");
                if (originalSourceLines[e.moduleName]) {
                    var lines = originalSourceLines[e.moduleName];
                    for (var i = e.lineNumber - 1; i <= e.lineNumber + 1; i++) {
                        if (lines[i-1]) {
                            stderr_write(padToFour(i) + ": " + lines[i-1] + "\n");
                        }
                    }
                    stderr_write("");
                }
            }
            if (e.stackFrames.length > 0 && this.printStackFrames) {
                stderr_write("\nStack frames:\n");
                for (i=0; i<e.stackFrames.length; i++) {
                    stderr_write("  " + e.stackFrames[i].methodName);
                    e.stackFrames[i].forEach(function(name, value) {
                        var debugString = "unknown";
                        try {
                            if (value === undefined) {
                                debugString = "‹undefined›";
                            } else {
                                debugString = callmethod(value,
                                    "asDebugString", [0])._value;
                            }
                        } catch(e) {
                            debugger;
                            debugString = "[Error calling asDebugString:" +
                                e.message._value + "]";
                        }
                        if (debugString.length > 60)
                            debugString = debugString.substring(0,57) + "...";
                        stderr_write("    " + name + " = " + debugString);
                    });
                }
            }
        } else if (e.exctype === "return") {
            this.stderr_write("ProgrammingError: you are attempting to return " +
                "from a method that has already returned, at line " +
                lineNumber + " of " + moduleName);
        } else if (e != "SystemExit") {
            this.stderr_write("Internal error around line " +
                lineNumber + " of " + moduleName + ": " + e);
            throw e;
        }
    } finally {
        if (Grace_prelude.methods["while(1)do(1)"])
            Grace_prelude.methods["while(1)do(1)"].safe = false;
    }
};

MiniGrace.prototype.run = function() {
    importedModules = {};
    do_import('standardGrace', gracecode_standardGrace);
    stackFrames = [];
    lineNumber = 1;
    moduleName = this.modname;
    eval(minigrace.generated_output);   // defines a global gracecode_‹moduleName›
    var theModuleFunc = window[graceModuleName(this.modname)];
    testpass = false;    // not used anywhere else ?
    if (Grace_prelude.methods["while(1)do(1)"])
        Grace_prelude.methods["while(1)do(1)"].safe = this.breakLoops;
    this.trapErrors(function() {
        if(document.getElementById("debugtoggle").checked) {
            GraceDebugger.cache.start();
            GraceDebugger.that = new GraceModule(this.modname);
            GraceDebugger.run(theModuleFunc, GraceDebugger.that);
        } else {
            do_import(this.modname, theModuleFunc);
        }
    });
};

// Returns true if the program was compiled, or false if the program has not been modified.
MiniGrace.prototype.compilerun = function(grace_code) {
    var compiled = false;
    if (grace_code != this.lastSourceCode ||
            this.mode != this.lastMode ||
            this.lastModule != document.getElementById("modname").value ||
            this.visDefault != document.getElementById("defaultVisibility").value) {
        loadDate = Date.now();
        this.compile(grace_code);
        this.lastSourceCode = grace_code;
        this.lastMode = this.mode;
        this.lastModule = document.getElementById("modname").value;
        this.visDefault = document.getElementById("defaultVisibility").value;        
        compiled = true;
    }
    if (!this.compileError && this.mode == 'js') {
        this.run();
    }
    return compiled;
};

var minigrace = new MiniGrace();
