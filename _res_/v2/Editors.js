/*

  AUTHOR
  Seagat2011 www.gitub.com/Seagat2011
  eterna.cmu.edu/web/player/90270/
  fold.it/port/user/1992490

  VERSION
  Major.Minor.Bugfix.Patch
  1.0.0.0

  DESCRIPTION
  (Basic) syntax-highlighter and text-formatter

  UPDATED

  REFERENCES

  COMPATIBILITY
  Chrome 53+
  
*/

function srcHighlighter(e){
  if(e && (e.srcElement.id=="axmEditor")){
    lineNumber.innerText = axmEditor
      .innerText
      .getLines()
      .map(function(_,idx){
        return "(" + ++idx + ")"
      }).join("\n")
  }
}

addEventListener("keyup",srcHighlighter,false);
addEventListener("keypress",srcHighlighter,false);