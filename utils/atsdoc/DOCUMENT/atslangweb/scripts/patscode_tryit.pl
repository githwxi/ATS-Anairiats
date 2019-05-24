#!/usr/bin/perl -w

use CGI;
#
#use JSON;
#use String::Random;
#

my $q = new CGI;

use constant PATSHOME => "/home/project-web/ats-lang/ATS-Postiats";
use constant PATSCC_PATH => PATSHOME."/bin/patscc";
use constant PATSOPT_PATH => PATSHOME."/bin/patsopt";

# Set this to where the assets are stored relative to the
# site's document root.
use constant ASSETS_PATH => "/TRYIT/.assets";

sub random_filename {
    my $length_of_randomstring=8;
#
# the length of the random string to generate
#
    my @chars=('a'..'z','A'..'Z','0'..'9','_');
    my $random_string;
    foreach (1..$length_of_randomstring) 
    {
	# rand @chars will generate a random 
	# number between 0 and scalar @chars
	$random_string.=$chars[rand @chars];
    }
    return $random_string;
#
#   $rand = new String::Random;
#   return $rand->randpattern("CnccCcCCncnCcnncCcnCnCcCnCnC");
#
}

sub file_of_string {
    local($filename, $content) = ($_[0], $_[1]);
    open(SOURCE,"+>",$filename) or die "Cannot create tmp file";
    print SOURCE $content;
    close(SOURCE);
}

# fork and exec a command, only giving errors if it exits
# with a non zero status.
sub fork_exec_err {
    @cmd = @_;
    pipe CCRD, CCWR;
    
    $pid = fork();
    die "Couldn't fork" unless defined $pid;
    if ( $pid > 0 ) {
        close(CCWR); wait();
    } else {
        close(CCRD);
        open(STDERR, ">&CCWR");
        open(STDOUT, ">", "/dev/null");
        exec { $cmd[0] } @cmd or die "Couldn't run compiler..";
    }
    $success = !$?;
    
    $msg = "";
    
    if(!$success) {
        $msg .= "Error:\n";
        while($line = <CCRD>) { $msg .= $line; }
    }
    return $success, $msg;
}

# Allow the user to define the method through 
# form input.
sub get_action {
    local($query) = ($_[0]);
    
    $method = $query->param("_method");
    if ($method) {
	return $method;
    } else {
	return $query->request_method();
    }
}

sub typecheck {
    local($query) = ($_[0]);
    $output = "";    

    #Create the temporary file
    $name = "/tmp/".random_filename().".dats";    
    file_of_string($name, $query->param('input'));
    @cmd  = (PATSCC_PATH, "-tcats", "-IATS ${PATSHOME}/contrib", $name);

    #Run it through the typechecker
    $ENV{"PATSHOME"} = PATSHOME; $ENV{"PATSOPT"} = PATSOPT_PATH;
    ($success, $msg) = fork_exec_err(@cmd);
    $output = $success ? "Your code has been successfully typechecked!" : $msg;
    
    #If there's an error, reformat the output so the editor can highlight the errors.
    if (!$success) {
        $output = CGI::escapeHTML($output);

        $final = "";
        @lines = split("\n",$output);
        
        foreach $line (@lines) {
            if($line =~ /^(\/tmp|syntax error)/) {
                $line =~ s/\(line=(\d+), offs=(\d+)\).*?\(line=(\d+), offs=(\d+)\)/<button class="syntax-error range-error" data-line-start="$1" data-char-start="$2" data-line-end="$3" data-char-end="$4">($1,$2) to ($3,$4)<\/button>/;
            }
            $final .= $line."\n";
        }
        $output = $final;
    }
    
    #clean up
    unlink $name;

#
#   print encode_json({"status"=>!$success,"output"=>$output});
#

#
#  encode a json string
#
   $status = $success ? 0 : 1;
   $output =~ s/("|\\|\/)/\\$1/g;
   $output =~ s/\n/\\n/g;
   $output =~ s/\t/\\t/g;
   $output =~ s/\f/\\f/g;
   $output =~ s/\r/\\r/g;
   print "{\"status\":$status, \"output\":\"$output\"}";
}

sub render_code {
    local($query) = ($_[0]);
    $code = $query->param('input');
    print $query->start_html(-title=>"Try ATS",
                             -style=>[
                                  {-src=>ASSETS_PATH."/bootstrap.css"},
                                  {-src=>ASSETS_PATH."/codemirror.css"},
                                  {-src=>ASSETS_PATH."/style.css"}
                             ],
                             -script=> [
                                  {-type=>'text/javascript',
                                   -src=>'https://ajax.googleapis.com/ajax/libs/jquery/1.7.2/jquery.min.js'},
                                  {-type=>'text/javascript',
                                   -src=>ASSETS_PATH.'/codemirror.js'},
                                  {-type=>'text/javascript',
                                   -src=>ASSETS_PATH.'/code.js'}
                             ]
	);
    
    #Display the editor
    print <<HTML;
    <div class="container-fluid">

    <div class="row-fluid">
    <div id="patsopt-container" class="span6">
    <h1>Try ATS</h1>
        <div id="patsopt" class="prettyprint">
        <textarea class="code-mirror">$code</textarea>
        </div>
    </div>
    <div id="patsopt-console" class="span6">
    <h2>Output</h2>
    <div id="patsopt-output" class="prettyprint">
    </div>
    </div>
    </div>
    <button class="btn" id="typecheck-btn">TypeCheck</button>
    </div>
HTML
    print $q->end_html();
}

# 2 ways to arrive here 
# POST from a documentation page.
# PUT from the coding page.

$action = get_action($q) ;
if( $action eq "POST") {
    print $q->header("text/html");
    render_code($q);
} elsif( $action eq "PUT") {
    print $q->header("text/json");
    typecheck($q);
}
