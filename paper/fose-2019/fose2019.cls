% fose.cls   Dec. 16, 2010 by Shinsuke MATSUMOTO
% fose.sty   Mar. 7, 2006 by FOSE2006
% fose.sty   Mar. 16, 2005 by FOSE2005
% fose03.sty Feb. 18, 1994 by Hideki ISOZAKI isozaki@ntt-20.ntt.jp
% compsoft.sty 2-December-91 by Yasuki SAITO
% compsoft.sty 18-July-90 by Hideki ISOZAKI
% j-article.sty 10-Feb-89 from report.sty 16-Mar-88

%\typeout{Document Style `fose' <Feb. 18, 1994>.}


\ifx\pfmtname\undefined
\NeedsTeXFormat{LaTeX2e}
\else
\NeedsTeXFormat{pLaTeX2e}
\fi

\ProvidesClass{fose2019}[2019/03/21 ver 1.00]


\def\ds@twoside{\@twosidetrue \@mparswitchtrue}
\def\ds@draft{\overfullrule5pt}

\newdimen\@maxsep
\newdimen\@dblmaxsep

%\@options
% you must do this at the end, at least after def's of \ds@... for
% various \@maketitle

\ds@twoside

\input fose2019.sty



\def\title{\@dblarg{\@xtitle}}
\def\@xtitle[#1]#2{\gdef\@title{#2}}
\def\@title{\leavevmode\mkt@warning\title}

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*{\cal}{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*{\mit}{\@fontswitch\relax\mathnormal}
\DeclareOldFontCommand{\mc}{\normalfont\mcfamily}{\mathmc}
\DeclareOldFontCommand{\gt}{\normalfont\gtfamily}{\mathgt}

\newif\if@eng \@engfalse
\newif\if@asc \@ascfalse

\DeclareOption{english}{\@engtrue}
\DeclareOption{ascii}{\@asctrue}

\@options

%\newif\if@asc
%  \DeclareOption{ascii}{\@asctrue}


\if@asc
 \setlength{\baselineskip}{0.5\baselineskip}
\fi

\def\labelenumi{\theenumi.} 
\def\theenumi{\arabic{enumi}} 
\def\labelenumii{(\theenumii)}
\def\theenumii{\alph{enumii}}
\def\p@enumii{\theenumi}
\def\labelenumiii{\theenumiii.}
\def\theenumiii{\roman{enumiii}}
\def\p@enumiii{\theenumi(\theenumii)}
\def\labelenumiv{\theenumiv.}
\def\theenumiv{\Alph{enumiv}} 
\def\p@enumiv{\p@enumiii\theenumiii}

\def\labelitemi{$\bullet$}
\def\labelitemii{$\circ$}
\def\labelitemiii{$\ast$}
\def\labelitemiv{$\cdot$}

\def\verse{\let\\=\@centercr 
 \list{}{\itemsep\z@ \itemindent -1.5em\listparindent \itemindent 
 \rightmargin\leftmargin\advance\leftmargin 1.5em}\item[]}
\let\endverse\endlist
\def\quotation{\list{}{\listparindent 1.5em
 \itemindent\listparindent
 \rightmargin\leftmargin \parsep 0pt}\item[]}
\let\endquotation=\endlist
\def\quote{\list{}{\rightmargin\leftmargin}\item[]}
\let\endquote=\endlist

\def\descriptionlabel#1{\hspace\labelsep \bf #1}
\def\description{\list{}{\labelwidth\z@ \itemindent-\leftmargin
 \let\makelabel\descriptionlabel}}
\let\enddescription\endlist



\def\theequation{\arabic{equation}}

\arraycolsep 5pt \tabcolsep 6pt \arrayrulewidth .4pt \doublerulesep 2pt 
\tabbingsep \labelsep 

\skip\@mpfootins = \skip\footins
\fboxsep = 3pt \fboxrule = .4pt 



\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\newcounter{subparagraph}[paragraph]

%\def\thepart{\Roman{part}} 
\def\thesection {\arabic{section}}
\def\thesubsection {\thesection.\arabic{subsection}}
\def\thesubsubsection {\thesubsection.\arabic{subsubsection}}
\def\theparagraph {\thesubsubsection.\arabic{paragraph}}
\def\thesubparagraph {\theparagraph.\arabic{subparagraph}}



% Do not delete BEFORESKIP even if \section is on top of page
% Is this functioning?
\def\@startsection#1#2#3#4#5#6{\if@noskipsec \leavevmode \fi
   \par \@tempskipa #4\relax
   \@afterindenttrue
   \ifdim \@tempskipa <\z@ \@tempskipa -\@tempskipa \@afterindentfalse\fi
   \if@nobreak \everypar{}\else
     \addpenalty{\@secpenalty}%
        \ifnum#2=\@ne%\message{topskip=\the\topskip,beforeskip=\the\@tempskipa}
%\message{prevdepth=\the\prevdepth}%
\ifdim\prevdepth=0pt\vspace*{-24\Q}\else\vskip-\prevdepth\fi
%\vspace{-\prevdepth} % seems to be the same as above, but does not work!!
%       \advance\@tempskipa-20\Q \addvspace{20\Q}
% 15.67pt = 20Q + depth(1.44539pt)
        \advance\@tempskipa-15.67pt \addvspace{15.67pt}
        \vspace*{\@tempskipa}%
        \else\addvspace{\@tempskipa}\fi\fi \@ifstar
     {\@ssect{#3}{#4}{#5}{#6}}{\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}}

% to include section/subsection title modification
\def\@sect#1#2#3#4#5#6[#7]#8{\ifnum #2>\c@secnumdepth
     \def\@svsec{}\else 
     \refstepcounter{#1}\edef\@svsec{\csname the#1\endcsname\hskip 1em }\fi
     \@tempskipa #5\relax
      \ifdim \@tempskipa>\z@ 
        \begingroup #6\relax
          \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty \@M 
                          \@mojidori{#8}\par}%
        \endgroup
       \csname #1mark\endcsname{#7}\addcontentsline
         {toc}{#1}{\ifnum #2>\c@secnumdepth \else
                      \protect\numberline{\csname the#1\endcsname}\fi
                    #7}\else
        \def\@svsechd{#6\hskip #3\@svsec #8\csname #1mark\endcsname
                      {#7}\addcontentsline
                           {toc}{#1}{\ifnum #2>\c@secnumdepth \else
                             \protect\numberline{\csname the#1\endcsname}\fi
                       #7}}\fi
     \@xsect{#5}}

\def\@ssect#1#2#3#4#5{\@tempskipa #3\relax
   \ifdim \@tempskipa>\z@
     \begingroup #4\@hangfrom{\hskip #1}{\interlinepenalty \@M \@mojidori{#5}\par}\endgroup
   \else \def\@svsechd{#4\hskip #1\relax #5}\fi
    \@xsect{#3}}

\newlength\@currentmojihaba

\ifx\jintercharskip\undefined

\def\nokinsoku@ascii{%
\typeout{Sorry, I don't know how to forget kinsoku rules.}
}

\def\@mojidori#1{\setbox0\hbox{#1}\settowidth{\@currentmojihaba}{あ}
 \ifdim\wd0>5\@currentmojihaba #1\else
  \ifdim\wd0<3\@currentmojihaba {\kanjiskip=2\@currentmojihaba #1}\else
   {\kanjiskip=0.2\@currentmojihaba 
    \xkanjiskip=0.3\@currentmojihaba 
    \nokinsoku@ascii
    #1}\fi\fi}

\else

\if@eng
 \def\nokinsoku@ntt{%
 \nokinsoku`ァ \nokinsoku`ィ \nokinsoku`ゥ %
 \nokinsoku`ェ \nokinsoku`ォ %
 \nokinsoku`ッ %
 \nokinsoku`ャ \nokinsoku`ュ \nokinsoku`ョ %
 \nokinsoku`ヮ \nokinsoku`ヵ \nokinsoku`ヶ %
 \nokinsoku`ー %
 }
\fi

\def\@mojidori#1{\setbox0\hbox{#1}\settowidth{\@currentmojihaba}{あ}
 \ifdim\wd0>5\@currentmojihaba #1\else
  \ifdim\wd0<3\@currentmojihaba % 2 kanjis or less
   {\jintercharskip=2\@currentmojihaba #1}%
  \else
   {\jintercharskip=0.2\@currentmojihaba 
    \jasciikanjiskip=0.3\@currentmojihaba 
    \jmathkanjiskip=\jasciikanjiskip
    \nokinsoku@ntt
    #1}\fi\fi}

\fi


\newlength\twodigits

\def\thebibliography#1{\subsection*{\refname}%
\vskip8\Q % = 25\Q - 17\Q (the difference in two baselineskips)
\settowidth\twodigits{#1}\list
 {~~[\hbox to \twodigits{\hss\arabic{enumi}\hss}]}
 {\setlength\labelwidth{10\Q}\leftmargin\labelwidth\labelsep\labelwidth
 \advance\leftmargin\labelsep
 \usecounter{enumi}\footnotesize\baselineskip=17\Q}
 \def\newblock{\hskip .11em plus .33em minus .07em}
 \sloppy\clubpenalty4000\widowpenalty4000
 \sfcode`\.=1000\relax}
\let\endthebibliography=\endlist

\if@eng
 \def\refname{References}
\else
 \def\refname{参考文献}
\fi



\newif\if@restonecol
\def\theindex{\@restonecoltrue\if@twocolumn\@restonecolfalse\fi
\twocolumn[\section*{\indexname}]
 \@mkboth{\indexname}{\indexname}\thispagestyle{plain}\parindent\z@
 \parskip\z@\relax\let\item\@idxitem}
\def\@idxitem{\par\hangindent 40pt}
\def\subitem{\par\hangindent 40pt \hspace*{20pt}}
\def\subsubitem{\par\hangindent 40pt \hspace*{30pt}}
\def\endtheindex{\if@restonecol\onecolumn\else\clearpage\fi}
\def\indexspace{\par}



% You may need to change following parameters
\setcounter{topnumber}{4} \def\topfraction{.9}
\setcounter{bottomnumber}{4} \def\bottomfraction{.9}
\setcounter{totalnumber}{8}
\def\textfraction{.1}
\def\floatpagefraction{.9}
\setcounter{dbltopnumber}{4} \def\dbltopfraction{.9}
\def\dblfloatpagefraction{.9}

% You cannot handle double column bottom figures yet!!!

\newskip\@beforecaptionskip
\newskip\@aftercaptionskip
% initial default values for under caption
\@beforecaptionskip=10\Q \@aftercaptionskip=0pt

\newbox\@tempboxb
% Following makecaption is for under caption.
% You may need to define another makecaption for over caption!!
\long\def\@makecaption#1#2{\vskip\@beforecaptionskip
 \setbox\@tempboxa\hbox{\footnotesize\bf #1\hskip10.02pt #2}
 \ifdim \wd\@tempboxa >\hsize
  \setbox\@tempboxb\hbox{\footnotesize\bf #1\hskip10.02pt}
  \hangindent=\wd\@tempboxb \hangafter=1
  {\footnotesize\bf #1\hskip10.02pt #2}\par \else
  \hbox to\hsize{\hfil\box\@tempboxa\hfil}
  \fi\vskip\@aftercaptionskip}

\newcounter{figure}
\def\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename \thefigure}
\def\figure{\bgroup
 \@beforecaptionskip=10\Q\@aftercaptionskip=0pt\@float{figure}}
\def\endfigure{\end@float\egroup}
\@namedef{figure*}{\bgroup
 \@beforecaptionskip=10\Q\@aftercaptionskip=0pt\@dblfloat{figure}}
\@namedef{endfigure*}{\end@dblfloat\egroup}

\newcounter{table}
\def\thetable{\@arabic\c@table}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename \thetable}
\def\table{\bgroup
  \@beforecaptionskip=0pt\@aftercaptionskip=7\Q\@float{table}}
\def\endtable{\end@float\egroup}
\@namedef{table*}{\bgroup
  \@beforecaptionskip=0pt\@aftercaptionskip=7\Q\@dblfloat{table}}
\@namedef{endtable*}{\end@dblfloat\egroup}

% height adjustment code insertion into float ending routines
\newdimen\@floatheight
\newcount\@floatlinecount

\def\end@float{\par\vskip\z@\egroup %% \par\vskip\z@ added 15 Dec 87
\@floatheight=\ht\@currbox
\advance\@floatheight \dp\@currbox
\divide\@floatheight\baselineskip \@floatlinecount=\@floatheight
\advance\@floatlinecount\@ne
\@floatheight=\@floatlinecount\baselineskip
%\fboxrule=0.01pt\fboxsep=0pt% for debugging
%\global\setbox\@currbox=\hbox{\fbox{\vbox to\@floatheight{\vfil\copy\@currbox\vfil}}}%
\global\setbox\@currbox=\vbox to\@floatheight{\vfil\copy\@currbox\vfil}%
   \ifnum\@floatpenalty <\z@
     \@cons\@currlist\@currbox
     \ifdim \ht\@currbox >\textheight 
        \ht\@currbox\textheight \fi
     \ifnum\@floatpenalty < -\@Mii 
        \penalty -\@Miv 
        \@tempdima\prevdepth    %% saving and restoring \prevdepth added
        \vbox{}                 %% 26 May 87 to prevent extra vertical
        \prevdepth \@tempdima   %% space when used in vertical mode
        \penalty\@floatpenalty
      \else \vadjust{\penalty -\@Miv \vbox{}\penalty\@floatpenalty}\@esphack
     \fi\fi}

\def\end@dblfloat{\if@twocolumn
     \par\vskip\z@\egroup %% \par\vskip\z@ added 15 Dec 87\egroup
\@floatheight=\ht\@currbox
\advance\@floatheight \dp\@currbox
\divide\@floatheight\baselineskip \@floatlinecount=\@floatheight
\advance\@floatlinecount\@ne
\@floatheight=\@floatlinecount\baselineskip
%\fboxrule=0.01pt\fboxsep=0pt% for debugging
%\global\setbox\@currbox=\hbox{\fbox{\vbox to\@floatheight{\vfil\copy\@currbox\vfil}}}%
\global\setbox\@currbox=\vbox to\@floatheight{\vfil\copy\@currbox\vfil}%
     \ifnum\@floatpenalty <\z@ \@cons\@dbldeferlist\@currbox\fi
      \ifnum \@floatpenalty =-\@Mii \@esphack\fi\else\end@float\fi}



\def\maketitle{\par
 \begingroup 
 \setcounter{footnote}{0} % Reset Thanks Counter
 \def\thefootnote{\fnsymbol{footnote}} % Use asterisks and daggers
 \def\@makefnmark{\hbox to 0pt{$^{\@thefnmark}$\hss}} 
 \newpage
 \global\@topnum\z@ \@maketitle \thispagestyle{empty}
 \let\ftnt@@\footnotetext \@affil
 \endgroup
 \setcounter{footnote}{0}} % Reset Footnote Counter

\if@asc
 \def\@maketitle{\newpage
 \setbox\@tempboxa\vbox\bgroup
 \leftline{\rule{\textwidth}{1mm}}
 \begin{flushleft} % Flushleft Author Line
  {\LARGE\bf \@title \par}\vskip 2mm\bf \@etitle
  \vskip 3mm {\Large\bf\let\fnmk@@\@xfootnotemark \@author}%
 \end{flushleft}\vskip 1cm\egroup\resize@boxa}
\else
 \def\@maketitle{\newpage
 \setbox\@tempboxa\vbox\bgroup
 \leftline{\rule{\textwidth}{1mm}}
 \begin{flushleft} % Flushleft Author Line
  {\LARGE\bf \@title \par}\vskip 2mm\bf \@etitle
  \vskip 3mm {\Large\bf\let\fnmk@@\@xfootnotemark \@author}%
 \end{flushleft}\vskip 5mm\egroup\resize@boxa}
\fi

\def\resize@boxa{%
\@tempdima\ht\@tempboxa
\advance\@tempdima\dp\@tempboxa
\advance\@tempdima 7.042pt % normalsize gap
\divide\@tempdima\baselineskip
\@tempcnta\@tempdima
\advance\@tempcnta\@ne
\@tempdima\baselineskip
\multiply\@tempdima\@tempcnta
\advance\@tempdima-8.625pt % -(gap+depth)
\vbox to \@tempdima{\unvbox\@tempboxa\vfill}}

% default title header

\def\ps@headings{\def\@oddfoot{}\def\@evenfoot{}
\def\@evenhead{\footnotesize\hfil \head@j \hfil}
%-- journalhead中で改行を許すように変更 + ページ番号を埋め込むための左右マージンを確保
%-- by shin 2011.10.12
% \def\@oddhead{\hbox{}\hfil\footnotesize\rm\title@j \hfil}
\def\@oddhead{\hbox{}\hfil\footnotesize\rm\parbox[t]{.9\columnwidth}{\centering\title@j} \hfil}
\def\sectionmark##1{\markboth {\uppercase{\ifnum \c@secnumdepth
>\z@
 \thesection\hskip 1em\relax \fi ##1}}{}}\def\subsectionmark##1{\markright
{\ifnum \c@secnumdepth >\@ne
 \thesubsection\hskip 1em\relax \fi ##1}}}


\def\leaderfill{\leaders\hbox{\rule{1mm}{1mm}}\hfill}



\mark{{}{}} 

\newcounter{volpage}
\newcounter{volpageoffset} % You must set this to appropriate value
\setcounter{volpageoffset}{0} % for each issue!

\pagenumbering{arabic}

\if@eng
 \def\tablename{Tab.}
 \def\figurename{Fig.}
 \def\today{\the\year/\the\month/\the\day }
\else
 \def\tablename{表}
 \def\figurename{図}
 \def\today{\the\year 年 \the\month 月 \the\day 日}
\fi


%\def\bf{\protect\pdg\protect\pbf}
%\def\bf{\protect\pbf}

\def\sloppy{\tolerance 9000 \hfuzz .5\p@ \vfuzz .5\p@}

\flushbottom



% To balance the final page,
% following code is borrowed from nicetwocolumn style
\newdimen\dimen@@

\def\balancecolumns{\setbox0\vbox{\unvbox\@outputbox} \dimen@@=\ht0
   \advance\dimen@@ by\topskip \advance\dimen@@ by-\baselineskip
   \divide\dimen@@ by2 \splittopskip=\topskip
   {\vbadness=10000 \loop \global\setbox3=\copy0
     \global\setbox1=\vsplit3 to\dimen@@
     \ifdim\ht3>\dimen@@ \global\advance\dimen@@ by1pt\repeat}
   \ifdim\dimen@@>\textheight \dimen@@=\textheight\fi
   \setbox0=\vbox to \dimen@@{\unvbox1} \setbox2=\vbox to \dimen@@{\unvbox3}
   \if\ht0>\ht2 \setbox2=\vbox to\ht0{\unvbox2}\dimen@@=\ht0\else
   \if\ht2>\ht0 \setbox0=\vbox to\ht2{\unvbox0}\dimen@@=\ht2\fi\fi
  \wd0=\hsize \wd2=\hsize
\ifdim\dp0>\dp2\advance\dimen@@ by\dp0\else\advance\dimen@@ by\dp2\fi
\setbox\@outputbox\vbox to\dimen@@{\hbox to\textwidth{\box0\hfil\box2}\vfill}}

% you can refrain from balancing by falsifying following switch!
\newif\if@lastpagebalancing \@lastpagebalancingtrue % default is to balance

% incorporate balanced output to \enddocument
\def\enddocument{\if@lastpagebalancing \global\let\@outputdblcol=\balancing@outputdblcol\fi%
\@checkend{document}\clearpage
\begingroup  
\if@filesw \immediate\closeout\@mainaux 
\def\global\@namedef##1##2{}\def\newlabel{\@testdef r}%
\def\bibcite{\@testdef b}\@tempswafalse \makeatletter\input \jobname.aux
\if@tempswa \@warning{Label(s) may have changed.  Rerun to get
cross-references right}\fi\fi\endgroup
\deadcycles\z@\@@end}

\newlength{\@interlinegap}


% to change \interlinegap appropriately at appropriate time
\def\jst@outputdblcol{\if@firstcolumn \global\@firstcolumnfalse
    \global\setbox\@leftcolumn\box\@outputbox
% Following interlinegap value may be wrong!!
% It is set to gap+depth for normalsize, and depth(2.031999Q) for footnotesize.
% This setting is inconsistent, but seems to work properly now.
%\ifx \@currsize\normalsize \global\@interlinegap 8.54815pt\else% setup
% reset to 10Q after final page footnote hack!
\ifx \@currsize\normalsize \global\@interlinegap 10\Q\else% setup
 \ifx \@currsize\footnotesize \global\@interlinegap 2.03199\Q\else% appropriate
  \ifx \@currsize\small \global\@interlinegap 3.08713pt\fi\fi\fi% gap here!
  \else \global\@firstcolumntrue
\if@leftfootnoteexist\setbox\@leftcolumn\vbox to\@colht{\boxmaxdepth\maxdepth
\@texttop\dimen128=\dp\@leftcolumn
\unvbox\@leftcolumn\vskip\skip\footins\footnoterule%
%\message{in outputdblcol leftcolumnfootnote=ht:\the\ht\@leftcolumnfootnote, dp:\the\dp\@leftcolumnfootnote, wd:\the\wd\@leftcolumnfootnote}
\unvbox\@leftcolumnfootnote
\vskip-\dimen128\@textbottom}
\global\maxdepth\@maxdepth\else
\setbox\@leftcolumn\vbox to\@colht{\boxmaxdepth\maxdepth
\@texttop\dimen128=\dp\@leftcolumn
\unvbox\@leftcolumn\vfill%
\vskip-\dimen128\@textbottom}
\global\maxdepth\@maxdepth\fi
\if@rightfootnoteexist\setbox\@outputbox\vbox to\@colht{\boxmaxdepth\maxdepth
\@texttop\dimen128=\dp\@outputbox
\unvbox\@outputbox\vskip\skip\footins\footnoterule%
%\message{in outputdblcol rightcolumnfootnote=ht:\the\ht\@rightcolumnfootnote, dp:\the\dp\@rightcolumnfootnote, wd:\the\wd\@rightcolumnfootnote}
\unvbox\@rightcolumnfootnote
\vskip-\dimen128\@textbottom}
\global\maxdepth\@maxdepth\else
\setbox\@outputbox\vbox to\@colht{\boxmaxdepth\maxdepth
\@texttop\dimen128=\dp\@outputbox
\unvbox\@outputbox\vfill%
\vskip-\dimen128\@textbottom}
\global\maxdepth\@maxdepth\fi
    \setbox\@outputbox\vbox{\hbox to\textwidth{\hbox to\columnwidth
      {\box\@leftcolumn \hss}\hfil \vrule width\columnseprule\hfil
       \hbox to\columnwidth{\box\@outputbox \hss}}}\@combinedblfloats
       \@outputpage \begingroup \@dblfloatplacement \@startdblcolumn
       \@whilesw\if@fcolmade \fi{\@outputpage\@startdblcolumn}\endgroup
    \fi}

\def\balancing@outputdblcol{\if@firstcolumn %\global\@firstcolumnfalse
 \else \global\@firstcolumntrue
  \setbox\@outputbox\vbox{\unvbox\@leftcolumn\vskip\@interlinegap%
   \penalty\interlinepenalty\unvbox\@outputbox}
 \fi
 \balancecolumns \@combinedblfloats
\if@leftfootnoteexist\setbox\@outputbox\vbox to\@colht{\boxmaxdepth\maxdepth
\@texttop\dimen128=\dp\@outputbox
\unvbox\@outputbox\vfill\vskip\skip\footins\footnoterule%
%\message{in balancing@outputdblcol leftcolumnfootnote=ht:\the\ht\@leftcolumnfootnote, dp:\the\dp\@leftcolumnfootnote, wd:\the\wd\@leftcolumnfootnote}
\unvbox\@leftcolumnfootnote
\if@rightfootnoteexist
%\message{in balancing@outputdblcol rightcolumnfootnote=ht:\the\ht\@rightcolumnfootnote, dp:\the\dp\@rightcolumnfootnote, wd:\the\wd\@rightcolumnfootnote}
\unvbox\@rightcolumnfootnote\fi
\vskip-\dimen128
\@textbottom}
\global\maxdepth\@maxdepth\fi
 \@outputpage \begingroup \@dblfloatplacement \@startdblcolumn
 \@whilesw\if@fcolmade \fi{\@outputpage\@startdblcolumn}\endgroup}

\newbox\@leftcolumnfootnote \newbox\@rightcolumnfootnote
\newif\if@leftfootnoteexist \newif\if@rightfootnoteexist

% Extra \@texttop somehow found its way into \@makecol.  Deleted
% 1 Dec 86.  (Found by Mike Harrison)

\def\jst@makecol{\if@firstcolumn
\ifvoid\footins \setbox\@outputbox\box\@cclv
%\message{in makecol @outputbox=(\the\ht\@outputbox, \the\dp\@outputbox, \the\wd\@outputbox)}
\global\@leftfootnoteexistfalse
   \else\global\@leftfootnoteexisttrue
\setbox\@outputbox\box\@cclv
%\message{in makecol with foot @outputbox=(\the\ht\@outputbox, \the\dp\@outputbox, \the\wd\@outputbox)}
\global\setbox\@leftcolumnfootnote\box\footins
%\message{in makecol leftcolumnfootnote=ht:\the\ht\@leftcolumnfootnote, dp:\the\dp\@leftcolumnfootnote, wd:\the\wd\@leftcolumnfootnote}
\fi
     \xdef\@freelist{\@freelist\@midlist}\gdef\@midlist{}\@combinefloats
\else
\ifvoid\footins \setbox\@outputbox\box\@cclv
%\message{in makecol right @outputbox=(\the\ht\@outputbox, \the\dp\@outputbox, \the\wd\@outputbox)}
\global\@rightfootnoteexistfalse
   \else\global\@rightfootnoteexisttrue
\setbox\@outputbox\box\@cclv
%\message{in makecol right with foot @outputbox=(\the\ht\@outputbox, \the\dp\@outputbox, \the\wd\@outputbox)}
\global\setbox\@rightcolumnfootnote\box\footins
%\message{in makecol rightcolumnfootnote=ht:\the\ht\@rightcolumnfootnote, dp:\the\dp\@rightcolumnfootnote, wd:\the\wd\@rightcolumnfootnote}
\fi
     \xdef\@freelist{\@freelist\@midlist}\gdef\@midlist{}\@combinefloats
\fi
}

\if@twocolumn
\let\@makecol\jst@makecol
\let\@outputdblcol\jst@outputdblcol
\fi

\long\def\@makefntext#1{\noindent$\@thefnmark$\hskip10\Q #1}

\def\@makefnmark{\smash{\hbox{$^{\@thefnmark}$}}} % smashed to make it
                                                  % zero height
% Following \footnoterule is changed to make a gap between footnoterule
% and first footnote text about 2Q.
%\def\footnoterule{\kern-3\p@ \hrule width 35mm \kern 2.6\p@} 
\def\footnoterule{\kern0\p@ \hrule width 35mm \kern-0.4\p@}





% to add extra space before citation by yamanouchi
\def\cite{{\hskip 3pt}\@ifnextchar [{\@tempswatrue\@citex}{\@tempswafalse\@citex[]}}

\def\@citex[#1]#2{\if@filesw\immediate\write\@auxout{\string\citation{#2}}\fi
        \def\@citea{}%
        {\footnotesize\@for\@citeb:=#2\do
%               {\@citea\def\@citea{\penalty\@m\ }%
                {\@citea\def\@citea{\penalty\@m{\hskip 3pt}}%
                 \@ifundefined{b@\@citeb}%
                        {{\bf ?}\@warning{Citation 
                                `\@citeb' on page \thepage \space undefined}}%
                \hbox{[\csname b@\@citeb\endcsname]}}}}

% inclusion from motoyoshi's revision
\def\eqalignno#1{\displ@y \tabskip=30.06pt %\tabskip=3*11pt_kanji_width
  \halign to\displaywidth{\hfil$\@lign\displaystyle{##}$\tabskip=\z@skip
    &$\@lign\displaystyle{{}##}$\hfil\tabskip=0pt plus 1000pt minus 1000pt
    &\llap{$\@lign##~~~$}\tabskip=\z@skip\crcr
    #1\crcr}}

% height adjusting environment
% you must use this as separate paragraph

\newbox\adjustbox
\newdimen\adjustheight
\newcount\adjustlinecount

\newenvironment{adjustvboxheight}{%\message{prevdepth=\the\prevdepth}
\vskip-\prevdepth\vskip1.4454pt % to cancel out various depth and set
                               % it to normal 1.445pt.  For this to
                               % work properly, it is necessary to use
                               % this environment as a separate paragraph!!
\global\setbox\adjustbox=\vbox\bgroup
\hsize\columnwidth }{\egroup
\adjustheight=\ht\adjustbox
\advance\adjustheight \dp\adjustbox
\divide\adjustheight\baselineskip \adjustlinecount=\adjustheight
\advance\adjustlinecount by 1
\adjustheight=\adjustlinecount\baselineskip
% you must ajust the position of top box somehow!!!
\vskip-.5\Q\vskip-1.445pt\vspace*{.5\Q}\vspace*{1.445pt}
%\fboxrule=0.01pt\fboxsep=0pt% for debugging
\vskip5\Q % = 1/2 gap
%\noindent\fbox{\vbox to\adjustheight{\vfil\box\adjustbox\vfil}}%
\noindent\vbox to\adjustheight{\vfil\box\adjustbox\vfil}%
\vskip-5\Q % = 1/2 gap
\vskip-1.445pt\noindent}

\clubpenalty=-1000 \widowpenalty=-1000 % we allow club and widow lines ?

% The following redefinition influences \linebreak etc.
\def\sloppy{\tolerance 9999 \hfuzz .5\p@ \vfuzz .5\p@}

% use twocolumn instead of multicol
%\twocolumn

\vbadness10001 \hbadness5000
\tolerance 9999 \pretolerance\m@ne

\binoppenalty=0
\relpenalty=0

%\@options

\def\etitle#1{\gdef\@etitle{#1}}

\let\@author\empty
\let\@affil\empty

\let\ftnt@@\relax
\let\fnmk@@\relax

\def\author#1#2{%
\advance\c@footnote\@ne
\ifx\@author\empty
   \edef\@author{#1\fnmk@@[\the\c@footnote]}%
\else
   \edef\@author{\@author\quad#1\fnmk@@[\the\c@footnote]}%
\fi
\edef\@affil{\@affil\ftnt@@[\the\c@footnote]{#2}}}

\long\def\@makefntext#1{\parindent 1em\noindent
            \hbox to 1.8em{\hss$\m@th^{\@thefnmark}$}#1}

\if@eng
  \def\abstract{\vskip7.042pt % normalsize gap
  \setbox\@tempboxa\vbox\bgroup\noindent\hskip0.1\textwidth
     \begin{minipage}{0.8\textwidth}
     \parindent 10.02pt \small\noindent{\bf Summary.\ }}
\else
  \def\abstract{\vskip7.042pt % normalsize gap
  \setbox\@tempboxa\vbox\bgroup\noindent\hskip0.1\textwidth
     \begin{minipage}{0.8\textwidth}
     \parindent 10.02pt \small\noindent{\bf あらまし\ }}
\fi

\def\endabstract{\end{minipage}\egroup\resize@boxa}

\def\eabstract{\vskip7.042pt % normalsize gap
\setbox\@tempboxa\vbox\bgroup\noindent\hskip0.1\textwidth
   \begin{minipage}{0.8\textwidth}
   \parindent 10.02pt \small\noindent{\bf Summary.\ }}
\def\endeabstract{\end{minipage}\egroup\resize@boxa}


\def\journal#1#2#3{\gdef\volume@j{#1}\gdef\number@j{#2}\gdef\year@j{#3}}
\journal{0}{0}{\the\year}
\def\journalhead#1{\gdef\title@j{#1}}
\journalhead{\@etitle}

\def\booktitle#1{\gdef\head@j{#1}}
%\booktitle{FOSEXXX}

\if@eng
 \def\acknowledgements#1{\vspace{5mm}\par
   \noindent{{\gt Acknowledgements }}#1}
\else
 \if@asc
  \def\acknowledgements#1{\vspace{5mm}\par
    \noindent{{\bf 謝辞 }}#1}
 \else
  \def\acknowledgements#1{\vspace{5mm}\par
    \noindent{{\gt 謝辞 }}#1}
 \fi
\fi

\def\endacknowledgements{\par}

\pagestyle{headings}



\booktitle{FOSE\the\year}

