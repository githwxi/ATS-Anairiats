//
// Author: William Blair (wdblair AT bu DOT edu)
// Start time: July, 2012
//
(function () {
    var patscode_tryit_bind_all, patscode_of_html;
    
    $(document).ready(function() { patscode_tryit_bind_all(); });

    patscode_tryit_bind_all = function() {
	$('.patscode_tryit').each(function(i,el) {
            var button, para, _this;
            _this = this;
            para = $("<p>");
            button = $("<button>").text("Try it yourself!");
            para.append(button);
            para.insertAfter($(this));
            button.bind("click", function() {
                var name, code, content, form;
                content = patscode_of_html( $(_this).html() );
                name = $(_this).attr("name");
		form = $("<form>");
		action = "http://www.ats-lang.org/"+name;
		form.attr("action",action);
/*
  action = "http://ats.illtyped.com/code/"+name;
                form.attr("action","http://ats.illtyped.com/code/"+name);
*/
		form.attr("name",'open-editor');
		form.attr("target","_blank");
		form.attr("method","post");
		form.attr("action",action);
                code = $("<textarea name='input'>");
                code.val(content);
                form.append(code);
                $("body").append(form);
                form.hide();
                form.submit();
		    });
        });
    };

    patscode_of_html = function(html) {
        var start, end;
	start = /<span class=(".*?"|.*?)>/gi;
        end = /<\/span>/gi;
        return html.replace(start,'').replace(end,'');
    };

}).call(this);
