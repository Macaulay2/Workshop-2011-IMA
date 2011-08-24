-- You may redistribute this file under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2
-- of the License, or any later version.

-----------------------------------------
-- Header
-----------------------------------------
newPackage (
    "GAP4M2",
    Version => "0.1", 
    Date => "24. August 2011",
    Authors => {{Name => "David Cook II", Email => "dcook@ms.uky.edu", HomePage => "http://www.ms.uky.edu/~dcook/"}},
    Headline => "an interface for GAP in Macaulay2",
    Configuration => {"path" => "", "workspace" => ""},
    DebuggingMode => true
)
 
-- Configuration:  Looks at ~/.Macaulay2/GAP4M2-init.m2
gap'path = (options GAP4M2).Configuration#"path";
gap'workspace = (options GAP4M2).Configuration#"workspace";
if gap'workspace == "" then gap'workspace = applicationDirectory() | "GAP4M2.workspace";

export { 
    "gapCall",
        "NoWorkspace",
    "gapCreateWorkspace",
        "AdditionalCall",
        "OverwriteOld",
    "gapHasWorkspace",
    "gapRemoveWorkspace"
}

-----------------------------------------
-- Code
-----------------------------------------

-- Calls GAP using the workspace.
gapCall = method(Options => {NoWorkspace => false});
gapCall String := opts -> str -> ( 
    if not instance(opts#NoWorkspace, Boolean) then error "Option NoWorkspace should be a Boolean.";
    if not opts#NoWorkspace and not gapHasWorkspace() then gapCreateWorkspace();
    infn := temporaryFileName();
    erfn := temporaryFileName();
    o := openOut infn;
    o << str << endl << "quit;" << endl;
    close o;
    callStr := "!" | gap'path | "gap -N -r -b -q" | (if not opts#NoWorkspace then " -L " | gap'workspace else "") | " <" | infn | " 2>" | erfn;
    r := lines try get openIn(callStr)
        else (
            er := lines get openIn erfn;
            removeFile infn; 
            removeFile erfn;
            if last separate(":", first er) == " not found" then error "GAP could not be found on the path [" | gap'path | "].";
            error("GAP terminated with the error [", er, "].");
        );
    removeFile infn;
    removeFile erfn;
    r
)

-- Creates the GAP workspace, if necessary.
gapCreateWorkspace = method(Options => {AdditionalCall => "", OverwriteOld => false});
installMethod(gapCreateWorkspace, opts -> () -> (
    if not instance(opts#AdditionalCall, String) then error "Option AdditionalCall should be a String.";
    if not instance(opts#OverwriteOld, Boolean) then error "Option OverwriteOld should be a Boolean.";
    if opts#OverwriteOld or not gapHasWorkspace() then gapCall(opts.AdditionalCall | "\n" | "SaveWorkspace(\"" | gap'workspace | "\");\n quit;\n", NoWorkspace => true);
))

-- Checks for the existence of the GAP workspace.
gapHasWorkspace = method();
installMethod(gapHasWorkspace, () -> fileExists gap'workspace)

-- Removes the GAP workspace, if it exists.
gapRemoveWorkspace = method();
installMethod(gapRemoveWorkspace, () -> if fileExists gap'workspace then removeFile gap'workspace)

-----------------------------------------
-- Documentation
-----------------------------------------
beginDocumentation()

-- GAP4M2
doc ///
    Key
        GAP4M2
    Headline
        Package for interfacing Macaulay2 with GAP
    Description
        Text
            This package provides a basic interface from Macaulay2 to GAP.  The
            code automatically handles a workspace from which GAP is used.  Using
            workspaces allows GAP to quickly load for more rapid calls.

            The configuration file @TT "~/.Macaulay2/GAP4M2-init.m2"@ contains two
            configuration data points: @TT "path"@ and @TT "workspace"@.  The @TT "path"@
            refers to the location of the GAP executable itself.  If, however, GAP is
            on the system path, then this can be left blank.  The @TT "workspace"@ 
            allows the user to configure where the workspace will be stored.  It
            is always named @TT "GAP4M2.workspace"@.
///

-- gapCall
doc ///
    Key
        gapCall
        (gapCall, String)
        [gapCall, NoWorkspace]
        NoWorkspace
    Headline
        calls GAP and executes a string
    Usage
        r = gapCall str
        r = gapCall(str, NoWorkspace => true)
    Inputs
        str:String
            containing GAP commands to be executed
        NoWorkspace=>Boolean
            turns off using the Workspace created by Macaulay2
    Outputs
        r:List
            containing all the lines of outputted text from GAP
    Description
        Text
            This method executes GAP on a @TO "String"@ of commands and
            returns a @TO "List"@ containing the output text from GAP.
            The user is expected to parse the GAP results themselves.
        Example
            "TODO: This should be in a PRE environment."
            L = gapCall("1+1; 1+2; 1+3;")
            instance(first L, String)
            L' = value \ L
            sum L'
        Text
            If the GAP workspace does not exist (@TO "gapHasWorkspace"@)
            and the user has not specified @TT "NoWorkspace"@, then a 
            new workspace is created (@TO "gapCreateWorkspace"@).
    SeeAlso
        gapCreateWorkspace
///

-- gapCreateWorkspace
doc ///
    Key
        gapCreateWorkspace
        1:(gapCreateWorkspace)
        [gapCreateWorkspace, AdditionalCall]
        [gapCreateWorkspace, OverwriteOld]
        AdditionalCall
        OverwriteOld
    Headline
        creates a GAP workspace
    Usage
        gapCreateWorkspace()
        gapCreateWorkspace(AdditionalCall => String)
        gapCreateWorkspace(OverwriteOld => Boolean)
    Inputs
        AdditionalCall=>String
            contains additional code to be executed and saved as part of the workspace
        OverwriteOld=>Boolean
            determines whether an already extant workspace will be overwritten
    Description
        Text
            This method creates a new GAP workspace.  It will only overwrite an old
            workspace if told to via the @TT "OverwriteOld"@ option.  The user can 
            optionally run extra commands which are stored in the workspace (such
            as loading packages) via the @TT "AdditionalCall"@ option.
    Caveat
        The GAP workspace exists in the @TT "~/.Macaulay2"@ directory and takes several
        megabytes of space.  If this is a concern, then when calling @TO "gapCall"@ the
        user should use the @TO "NoWorkspace"@ option.
    SeeAlso
        gapHasWorkspace
        gapRemoveWorkspace
///

-- gapHasWorkspace
doc ///
    Key
        gapHasWorkspace
        1:(gapHasWorkspace)
    Headline
        determines if a GAP workspace exists
    Usage
        gapHasWorkspace()
    Description
        Text
            Determines if the GAP workspace which Macaulay2 will use exists.
    SeeAlso
        gapCreateWorkspace
///

-- gapRemoveWorkSpace
doc ///
    Key
        gapRemoveWorkspace
        1:(gapRemoveWorkspace)
    Headline
        removes an extant GAP workspace
    Usage
        gapRemoveWorkspace()
    Description
        Text
            Removes an extant GAP workspace.
    SeeAlso
        gapCreateWorkspace
        gapHasWorkspace
///

-----------------------------------------
-- Tests
-----------------------------------------

