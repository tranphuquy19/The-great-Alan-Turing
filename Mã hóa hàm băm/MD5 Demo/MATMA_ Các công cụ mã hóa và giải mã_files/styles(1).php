/**************************************
 * THEME NAME: college15_fixed
 *
 * Files included in this sheet:
 *
 *   college15_fixed/styles_layout.css
 *   college15_fixed/styles_fonts.css
 *   college15_fixed/styles_color.css
 **************************************/

/***** college15_fixed/styles_layout.css start *****/

/*******************************************************************
 styles_layout.css
  
 This CSS file contains all layout definitions like positioning,
 floats, margins, paddding, borders etc.

 Styles are organised into the following sections:
  core
  header
  footer

  admin
  blocks
  calendar
  course
  doc
  grades
  login
  message
  tabs
  user

  various modules

*******************************************************************/


/***
 *** Core
 ***/

h1.main,
h2.main,
h3.main,
h4.main,
h5.main,
h6.main {
  text-align: center;
}

#layout-table {
  width:100%;
  border-collapse:separate;
  margin-top: 8px;
}

#layout-table #left-column,
#layout-table #middle-column,
#layout-table #right-column
{
  vertical-align:top;
}

#layout-table #middle-column {
  padding-left:12px;
  padding-right:12px;
}


.clearer {
  clear:both;
  margin:0px;
  padding:0px;
  height:1px;
  border:none;
  background:transparent;
}

.continuebutton {
  text-align: center;
}

form {
  margin-bottom:0px;
}

table {
  border-spacing: 0px;
  border-collapse: collapse;
}

a img {
  border:none;
}
.notifyproblem {
  text-align: center;
  padding: 10px;
}
  
.notifysuccess {
  text-align:center;
  padding: 10px;
}   

.generalbox {
  border-width:1px;
  border-style:solid;
  margin-bottom: 15px;
}

.generalbox#intro {
  text-align:center;
}

.noticebox {
  border-width:1px;
  border-style:solid;
}
.errorbox {
  border-width:1px;
  border-style:solid;
  margin: 1em 15%;
  width: 70%;
}
.errorbox .title {
  padding: 5px;
}

.informationbox {
  border-width:1px;
  border-style:solid;
}
.feedbackbox {
  border-width:1px;
  border-style:solid;
}
.feedbackby {
}
.feedback {
}
.initialbar {
  text-align: center;
}

#help .indent {
  margin-left:3em;
}

.tabledivider {
  border-width:1px;
  border-style:solid;
  border-left:0px;
  border-right:0px;
  border-top:0px;
}

.sitetopic {
  margin-bottom:20px;
}

.sitetopiccontent {
  border-width:1px;
  border-style:solid;
}

.pagingbar {
  text-align:center;
}
.pagingbar a {
  padding-left: 10px;
}
.pagingbar .thispage {
  padding-left: 10px;
}

table.formtable {
  margin: auto;
}

table.formtable tbody th {
  vertical-align: top;
}

table.formtable tbody td,
table.formtable tbody th
{
  padding: 5px;
}

.paging {
  text-align: center;
  margin: 10px 0px 10px 0px;
}

.unread {
  padding-right:2px;
} 

.cell {
  vertical-align: top;
}

.helplink img {
  vertical-align: middle;
  margin: 0px 2px;
}

form.popupform {
  display: inline;
}

/***
 *** Header
 ***/

#header-home {
}

#header {
}

.topic{
	background-color:#B2C3DB;
}
.sideblock{
	background-image:url(gradient.gif);
}
/*.header {
	background-image:url(gradient.gif);
	background-color:#B2C3DB;
}*/

.headermain {
	float:left;
	vertical-align:bottom;
}

.headermenu {
	float:right;
}

.navbar {
  width:100%;
  padding:1px 0.5em;
  height:1.3em;
  border-width:1px;
  border-style:solid;
  background-color:#B2C3DB;
  background-image:url(navbar_bg.gif);
}

.navbar .breadcrumb {
  float:left;
  margin:0.2em 0em;
}

.navbar .navbutton,
.navbar .menu {
  float:right;
}

#footer .navbar {
  margin-top: 4em;
}

.reportlink {
  text-align:right;
}


/***
 *** Footer
 ***/

#footer {
  text-align:center;
  margin-top: 100px;
}

.homelink {
  margin: 1em 0;
}

.homelink a {
  padding-left:1em;
  padding-right:1em;
}

.performanceinfo {
  margin: 2em;
}

.performanceinfo span {
  display: block;
}



/***
 *** Admin
 ***/

body#admin-index .c0 {
  vertical-align: top;
} 

body#admin-modules table.generaltable td.cell,
body#admin-modules .generaltablecell {
  padding-top: 2px;
  padding-bottom: 2px;
} 

body#admin-blocks table.generaltable td.cell,
body#admin-blocks .generaltablecell {
  padding-top: 1px;
  padding-bottom: 1px;
} 

body#admin-config .confighelp {
  display: block;
  padding-bottom: 20px;
}


/***
 *** Blocks
 ***/

.sideblock .content h3,
.sideblock .content h2 {
  text-align: left;
}

.sideblock {
  margin-bottom:1em;
  width: 100%;
}

.sideblock .header {
  text-align: left;
  padding:4px;
  border-width: 1px;
  border-style: solid;
  border-bottom: none;
}

.sideblock .header .hide-show {
  float:right;
}

.sideblock .header .hide-show img.hide-show-image {
  height:11px;
  width:11px;
  margin-top:0.25em;
}

.sideblock .header .commands {
  margin-top: 0.3em;
  clear: both;
}

.sideblock .header .commands a {
  margin: 0px 2px;
}

.sideblock .content {
  padding: 4px;
  border-width: 1px;
  border-style: solid;
}

.sideblock .content hr {
  height:1px;
  margin-top:4px;
  margin-bottom:4px;
  border:none;
  border-top:1px solid;
}

#left-column .hidden .header,
#right-column .hidden .header
{
  border-bottom-width: 1px;
  border-bottom-style: solid;
}

#left-column .hidden .content,
#right-column .hidden .content
{
  display: none;
}

.sideblock .list {
  width: 100%;
}

.sideblock .list .c0{
  padding: 2px;
}

.sideblock .footer {
  margin-bottom: 4px;
  text-align:center;
}

.sideblock .header .icon.hide,
.sideblock .header .icon.edit {
  margin-right: 6px;
}

.sideblock .content .head {
  margin-top: 10px;
}


/***
 *** Calendar
 ***/

#calendar {
  width: 100%;
  border-spacing: 5px;
  border-collapse: separate;
}

#calendar h2,
#calendar h3
{
  text-align: center;
}

#calendar .maincalendar,
#calendar .sidecalendar
{
  vertical-align: top;
  border: 1px solid;
}

#calendar .sidecalendar {
  width: 25%;
}

#calendar .maincalendar table.calendarmonth {
  border-collapse: separate;
  margin: 0px auto;
  width: 98%;
}

#calendar .maincalendar table.calendarmonth th {
  padding:10px;
  border-bottom:2px solid;
}

#calendar .maincalendar table.calendarmonth td {
  height: 5em;
  padding-left: 4px;
  padding-top: 4px;
  line-height:1.2em;
}

#calendar .maincalendar table.calendarmonth td,
table.minicalendar td,
table.minicalendar th {
  width:14%;
  vertical-align:top;
}
table.minicalendar td {
  text-align: center;
}
#calendar .maincalendar table.calendarmonth td table td {
  height: auto;
}

#calendar div.header
{
  padding: 5px;
}

#calendar .maincalendar .buttons {
  float: right;
}

#calendar .maincalendar .filters table,
#calendar .sidecalendar .filters table,
.sideblock.block_calendar_month .filters table
{
  border-collapse:separate;
  border-spacing: 2px;
  padding: 2px;
  width: 100%;
}

#calendar .maincalendar .filters {
  padding: 0px 10px;
}

#calendar .sidecalendar .filters {
  padding: 5px;
}

#calendar .maincalendar .controls {
  clear:both;
  padding:10px;
}

#calendar .maincalendar table.calendarmonth ul.events-new,
#calendar .maincalendar table.calendarmonth ul.events-underway
{
  padding:0px;
  margin:0px;
  list-style-type:none;
}

#calendar .maincalendar table.calendarmonth ul li {
  margin-top: 4px;
}

table.minicalendar {
  width: 100%;
  margin:10px auto;
  padding:2px;
  border-width:1px;
  border-style:solid;
  border-collapse:separate;
  border-spacing:1px !important;
}

table.minicalendar th {
  padding: 0px 2px;
}

#calendar .maincalendar .eventlist {
  padding: 10px;
}

#calendar .maincalendar .eventlist .topic {
  padding: 5px;
  border-style:solid; 
  border-width: 0px;
  border-bottom-color: #EEEEEE;
  border-bottom-width: 1px;
}

#calendar .maincalendar .eventlist .event {
  width:100%;
  margin-bottom:10px;
  border-spacing:0px;
  border-collapse:separate;
  border-width:1px;
  border-style:solid;
}

#calendar .maincalendar .eventlist .event .name {
  float:left;
}

#calendar .maincalendar .eventlist .event .course {
  float:left;
  clear:left;
}

#calendar .maincalendar .eventlist .event .date {
  float:right;
}

#calendar .maincalendar .eventlist .event .description .commands {
  width:100%;
}

#calendar .maincalendar .eventlist .event .description {
  padding:5px;
}

#calendar .maincalendar .eventlist .event .picture {
  padding:8px;
}

#calendar .maincalendar .eventlist .event .side {
  width:32px;
}

#calendar #selecteventtype table {
  margin:auto;
}

#calendar .event_global,
#calendar .event_course,
#calendar .event_group,
#calendar .event_user,
.minicalendar .event_global,
.minicalendar .event_course,
.minicalendar .event_group,
.minicalendar .event_user {
  border:2px solid !important;
}

#calendar .duration_global,
#calendar .duration_course,
#calendar .duration_group,
#calendar .duration_user,
.minicalendar .duration_global,
.minicalendar .duration_course,
.minicalendar .duration_group,
.minicalendar .duration_user
{
  border-top:2px solid !important;
  border-bottom:2px solid !important;
}

#calendar .today,
.minicalendar .today {
  border:2px solid !important;
}
  
.cal_popup_bg {
  padding:0px;
  margin:0px;
  border:1px solid;
}

.cal_popup_close {
  margin-right:5px;
}

.cal_popup_caption {
  border-width:0px 0px 1px 0px;
  border-style:solid;
  padding-bottom:2px;
}

table.calendar-controls {
  width: 100%;
}

table.calendar-controls .previous,
table.calendar-controls .next
{
  width: 12%;
}
table.calendar-controls .previous {
  text-align: left;
}
table.calendar-controls .current {
  text-align: center;
}
table.calendar-controls .next {
  text-align: right;
}

#calendar .maincalendar .calendar-controls .previous,
#calendar .maincalendar .calendar-controls .next
{
  width: 30%;
}


/***
 *** Course
 ***/
.activitydate, .activityhead {
  text-align:center;
}

#course-view .section td {
  vertical-align:top;
}

#course-view .section .content {
  padding:5px;
  border-style:solid;
  border-width:1px;
  border-left:0px;
  border-right:0px;
}

#course-view .section .side {
  padding:5px;
  border-style:solid;
  border-width:1px;
}

#course-view .section .left {
  border-right:0px;
  text-align:center;
  width: 1.5em;
}

#course-view .section .right {
  border-left:0px;
  text-align:center;
  width: 1.5em;
}

#course-view .current .side {
}

#course-view .section .spacer {
  height:0.5em;
}

#course-view .section .weekdates {
}

.section .activity img.activityicon {
  vertical-align:middle;
  height:16px;
  width:16px;
}

.section img.movetarget {
  height:16px;
  width:80px;
}

body#course-view .unread {
  margin-left: 3em;
} 

body#course-enrol .generalbox {
  margin-top: 20px;
}
body#course-enrol .coursebox {
  margin-top: 20px;
}

body#course-user .graph {
  text-align: center;
}

body#course-user .section,
body#course-user .content {
  margin-left: 30px;
  margin-right: 30px;
}

body#course-user .section {
  border-width:1px;
  border-style:solid;
  padding:10px;
  margin-bottom: 20px;
}

body#course-user .section h2 {
  margin-top: 0px;
}


.headingblock {
  border-width:1px;
  border-style:solid;
  padding:5px;
}

.headingblock .link {
  text-align:right;
}

body#site-index .headingblock,
body#course-view .headingblock {
  margin-bottom: 9px;
}

.coursebox {
  margin-bottom: 8px;
}

.categoryboxcontent,
.courseboxcontent {
  border-width:1px;
  border-style:solid;
}

.courseboxcontent .cost {
  padding-top: 20px;
}


/***
 *** Doc
 ***/
body{
	margin: 0px 0px 0px 0px;
}


body#doc-contents h1 {
  margin: 1em 0px 0px 0px;
}

body#doc-contents ul {
  list-style-type: none;
  margin: 0px;
  padding: 0px;
  width: 90%;
}


/***
 *** Grades
 ***/

body#grade-index .grades {
  border-width:1px;
  border-style:solid;
  border-collapse: separate;
}

body#grade-index .grades td {
  border-width:0px 1px 0px 1px;
  border-style:solid;
  border-collapse: collapse;
}

body#grade-index .grades .header {
  vertical-align: top;
}

body#grade-index .grades .points,
body#grade-index .grades .percent,
body#grade-index .grades .weighted {
  text-align: right;
}



/***
 *** Login
 ***/

.loginbox .content {
  border-width:1px;
  border-style:solid;
  padding:15px;
}


/***
 *** Message
 ***/

.message .link {
  vertical-align:middle;
}

table.message .searchresults td {
  padding:5px;
  border-width:1px;
  border-style:solid;
  border-collapse:collapse;
  border-spacing:0px;
}
.message .summary .link {
  text-align:right;
}
.message .heading {
  text-align:center;
}

.message .note {
  text-align:center;
  padding:10px;
}

#message-user .commands span {
  margin-left:10px;
  margin-right:10px;
}

body#message-messages {
  padding:10px;
}


/***
 *** Logs
 ***/

.logtable td,
.logtable th {
  padding-left: 10px;
  padding-right: 10px;
}

.logtable th {
  text-align:left;
}

/***
 *** Tabs
 ***/

.tabs {
  width: auto;
  margin-bottom: 15px;
  border-collapse: collapse;
}

.tabs td {
  padding: 0px;
}

.tabs .side {
  width: 50%;
  border-style: solid;
  border-width: 0px 0px 1px 0px;
}

.tabrow {
  border-collapse:collapse;
  width:100%;
  margin: 1px 0px 0px 0px;
}

.tabrow td {
  padding:0 0 0px 14px;
  border-style: solid;
  border-width: 0px 0px 1px 0px;
}

.tabrow th {
  display:none;
}
.tabrow td .tablink {
  display:block;
  padding:10px 14px 4px 0px;
  text-align:center;
  white-space:nowrap;
  text-decoration:none;
}
.tabrow .last {
  display:block;
  padding:0px 1px 0px 0px;
}
          
.tabrow td.selected {
  border-width: 0px;
}


/***
 *** User
 ***/

.userinfobox {
  margin-bottom:5px;
  border-width: 1px;
  border-style: solid;
  border-collapse: separate;    
}

.userinfobox .left {
  padding: 10px;
  width: 100px;
  vertical-align: top;
}

.userinfobox .content {
  padding: 10px;
  vertical-align: top;
}

.userinfobox .links {
  width: 100px;
  padding: 5px;
  vertical-align: bottom;
}

.userinfobox .list td {
  padding: 3px;
}

.userinfobox .username {
  padding-bottom: 20px;
}    


table.userinfobox {
  width: 80%;
  margin-left: 10%;
  margin-right: 10%;
}

table.groupinfobox {
  width: 60%;
  margin-left: 20%;
  margin-right: 20%;
  border-width:1px;
  border-style:solid;
  margin-bottom: 20px;
}

.groupinfobox .left {
  padding: 10px;
  width: 100px;
  vertical-align: top;
}
body#user-index #longtimenosee {
  text-align:center;
}


/***
 *** Modules: Assignment
 ***/

/***
 *** Modules: Chat
 ***/

/***
 *** Modules: Choice
 ***/

/***
 *** Modules: Forum
 ***/

.forumheaderlist,
.forumpost {
  border-width:1px;
  border-style:solid;
  border-collapse:separate;
}

.forumpost {
  margin-top: 15px;
}


.forumpost .topic {
  padding: 4px;
  border-style:solid;
  border-width: 0px;
  border-bottom-width: 1px;
}

.forumpost .commands {
  padding-top: 0.5em;
  text-align:right;
  clear: both;
}

.forumpost .ratings {
  padding-top: 1em;
  text-align:right;
}

.forumpost .attachments {
  padding: 7px;
  text-align:right;
}

.forumpost .content {
  padding: 4px;
}

.forumpost .footer {
  padding-top: 0.5em;
  text-align:right;
}

.forumpost .link {
  padding-top: 0.5em;
  text-align:right;
}

.forumpost .left {
  width: 35px;
  padding: 4px;
  text-align: center;
  vertical-align: top;
}

.mod-forum .indent {
  margin-left: 30px;
}

body#user-view .forumpost,
.course .forumpost {
  width: 100%;
}

body#mod-forum-search .c0 {
  text-align: right;
}

body#mod-forum-search .introcontent {
  padding: 15px;
}

.forumolddiscuss {
  text-align: right;
}

.forumheaderlist {
  width: 100%;
}

.forumheaderlist td {
  border-width:1px 0px 0px 1px;
  border-style:solid;
 }

.forumheaderlist .replies {
  text-align: center;
  white-space: nowrap;
}

.forumheaderlist .picture {
  width: 35px;
}

.forumheaderlist .discussion .starter {
  vertical-align: middle;
}

.forumheaderlist .lastpost {
  white-space: nowrap;
  text-align: right;
}

.forumheaderlist .discussion .author {
  white-space: nowrap;
}
.forumolddiscuss {
  text-align:right;
}
.forumaddnew,
.forumnodiscuss,
.noticeboxcontent {
  text-align:center;
}
#mod-forum-view .unread {
  padding-left: 3px;
  padding-right: 3px;
}
#mod-forum-discuss .forumpost.unread .content {
  border-style: solid;
  border-width: 2px;
}
#mod-forum-index .unread img,
#mod-forum-view .unread img 
{
  margin-left: 5px;
}

#email .unsubscribelink {
  margin-top:20px;
  border-width: 0px 1px 0px 0px;
  border-style: solid;
  text-align:center;
}


/***
 *** Modules: Glossary
 ***/

.glossarypost .commands {
  width: 200px;
  white-space: nowrap;
}

.entryboxheader {
  border-width: 1px 1px 0px 1px;
  border-style: solid;
}

.entrybox {
  border-width: 0px 1px 1px 1px;
  border-style: solid;
}

.glossarypost {
  width: 95%;
  border-width:1px;
  border-style:solid;
  border-collapse:separate;
  margin-bottom: 5px;
  text-align: left;
}


.entrylist {
  border-width:0px;
}

.entrylowersection {
  padding-top: 10px;
}
.entrylowersection table{
  width: 100%;
}
.entrylowersection .aliases {
  text-align:center;
}
.entrylowersection .icons,
.entrylowersection .ratings {
  text-align:right;
  padding-right: 5px;
}
.entrylowersection .ratings {
  padding-bottom: 2px;
}
.categoryheader {
  width: 95%;
}
.glossaryformatheader {
  width: 90%;
}

.glossarypost .entry {
  padding: 3px;
}

.glossarypost .picture {
  width: 35px;
}

.glossarycomment {
  border-width:1px;
  border-style:solid;
  border-collapse:separate;
  margin-bottom: 5px;
  text-align: left;
}


.glossarycomment .entry {
  padding: 3px;
}

.glossarycomment .picture {
  width: 35px;
}

.glossarycomment .icons {
  text-align: right;
}

.glossarydisplay {
  width: 70%;
}

.glossarydisplay .tabs {
  width: 100%;
}

.glossarydisplay .separator {
  width: 4px;
}

.glossarydisplay .tabs .selected,
.glossarydisplay .tabs .inactive,
.glossarydisplay .tabs .general {
}

.glossarypopup {
  width: 95%;
}

.glossaryapproval {
  width: 100%;
}

.mod-glossary .tabs {
  margin-bottom: 0px;
}
.mod-glossary .tabs .side {
  border-style: none;
  border-width: 0px;
  width: auto;
}


/***
 *** Modules: Journal
 ***/
#mod-journal-view .lastedit,
#mod-journal-view .editend {
  margin: 5px;
  text-align: center;
}
#mod-journal-view .feedbackbox {
  width: 75%;
  border-collapse: separate;
}
#mod-journal-view .entrycontent {
  padding: 3px;
}
#mod-journal-view .picture {
  width: 35px;
}
#mod-journal-view .grade {
  text-align: right;
}
#mod-journal-view .info {
  margin-bottom: 5px;
  text-align: right;
}


/***
 *** Modules: Label
 ***/

/***
 *** Modules: Lesson
 ***/

/***
 *** Modules: Quiz
 ***/

.feedbacktext {
  display:block;
}

body#mod-quiz-report table#attempts,
body#mod-quiz-report table#commands
{
  width: 80%;
  margin: auto;
}
body#mod-quiz-report table#attempts {
  margin: 20px auto;
}
body#mod-quiz-report table#attempts .header,
body#mod-quiz-report table#attempts .cell
{
  padding: 4px;
}
body#mod-quiz-report table#attempts .header .commands {
  display: inline;
}
body#mod-quiz-report table#attempts .picture {
  width: 40px;
}
body#mod-quiz-report table#attempts td {
  border-left-width: 1px;
  border-right-width: 1px;
  border-left-style: solid;
  border-right-style: solid;
}
.feedbacktext {
  text-align:right;
}
body#mod-quiz-report table#attempts .header {
  text-align: left;
}
body#mod-quiz-report table#attempts .picture {
  text-align: center !important;
}
body#mod-quiz-report .controls {
  text-align: center;
}



/***
 *** Modules: Resource
 ***/

/***
 *** Modules: Scorm
 ***/

/***
 *** Modules: Survey
 ***/

/***
 *** Modules: Wiki
 ***/

/***
 *** Modules: Workshop
 ***/
/***** college15_fixed/styles_layout.css end *****/

/***** college15_fixed/styles_fonts.css start *****/

/*******************************************************************
 styles_color.css
  
 This CSS file contains all font definitions like family, size,
 weight, text-align, letter-spacing etc.

 Styles are organised into the following sections:
  core
  header
  footer

  admin
  blocks
  calendar
  course
  doc
  grades
  login
  message
  tabs
  user

  various modules

*******************************************************************/


/***
 *** Core
 ***/

.clearer {
  font-size:1px;
}

body, td, th, li {
  font-family: Verdana, Arial, Helvetica, sans-serif;
  font-size:12px;
  letter-spacing:0.02em;
}

th {
  font-weight: bold;
}

a:link,
a:visited {
  text-decoration:none;
}

a:hover {
  text-decoration: underline;
}

h1.main,
h2.main,
h3.main,
h4.main,
h5.main,
h6.main {
  font-weight:bold;
}

h1 {
  font-size:1.7em;
}

h2 {
  font-size:1.4em;
}
h3 {
  font-size:1.1em;
}
h4 {
  font-size:1.0em;
}

.bold {
  font-weight:bold;
}

.warning {
  font-weight: bold;
  font-style: italic;
}

.errorbox .title {
  font-weight: bold;
  font-size: 1.2em;
  text-align: center;
}

.pagingbar .title {
  font-weight: bold;
}
.pagingbar .thispage {
  font-weight: bold;
}

.categorybox .category,
.categorybox .category {
  font-size:1.2em;
  font-weight:bold;
}

.helplink {
  font-size:0.8em;
}

.headingblock {
  font-weight: bold;
}

.headingblock .link {
  font-size: 0.9em;
}

.files .file {
  font-size: 0.9em;
}

.files .folder {
  font-size: 0.9em;
}

.files .folder .size {
  font-weight: bold;
}


/***
 *** Header
 ***/

.headermain {
  font-weight:bold;
}

#header-home .headermain {
  font-size:1.5em;
}

#header .headermain {
  font-size:1.3em;
}

.breadcrumb {
  font-size:0.9em;
  font-weight:bold;
}

.headingblock{
	background-image: url(header.gif);
}

.forumheaderlist th{
	background-image:url(header.gif);
	height:24px;
}
.headermenu{
	font-size:11px;
	color:#FFFFFF;
}
a.headermenu{
	color:#FFFFFF;
}
.headermenu a:hover {
color: #ffffff;
}

.headermenu a:visited {
color: #ffffff;
}


.logininfo,
#header-home{
  font-size:0.9em;
}


/***
 *** Footer
 ***/

.homelink {
}


.performanceinfo {
  font-size: 0.6em;
}


/***
 *** Admin
 ***/

table.formtable tbody th {
  font-weight: normal;
  text-align: right;
}


/***
 *** Blocks
 ***/

.sideblock .header {
  font-size:0.9em;
  font-weight: bold;
}

.sideblock .content {
  font-size:12px;
  line-height:1.2em;
}

.sideblock .content h3,
.sideblock .content h2 {
  font-size:1.0em;
}
.sideblock .header .commands {
  font-size:0.9em;
}

.sideblock .footer {
  font-size:0.9em;
}

.sideblock .head,
.sideblock .info,
.sideblock .event {
  font-size: 0.9em;
}

.sideblock .date {
  font-style: italic;
}

.block_site_main_menu .footer select {
  font-size: 0.8em;
}

/***
 *** Calendar
 ***/

#calendar .maincalendar .eventlist .event .referer {
  font-weight:bold;
}

#calendar .maincalendar .eventlist .event .course {
  font-size:0.8em;
}

#calendar .maincalendar .eventlist .event .description .commands {
  text-align: right;
}

#calendar .maincalendar table.calendarmonth td {
  font-size:0.8em;
}

#calendar div.header
{
  font-weight:bold;
}

#calendar .sidecalendar .filters {
  font-size:0.8em;
}

.sideblock .filters td {
  font-size:1.1em;
}

#calendar .maincalendar .controls {
  font-size:1.2em;
}

#calendar .maincalendar .day {
  font-weight: bold;
}

table.minicalendar {
  font-size:0.85em;
}

.cal_popup_caption {
  font-family:sans-serif;
  font-size:0.8em;
  font-weight:bold;
}

.cal_popup_close {
  font-family:sans-serif;
  font-size:0.8em;
  font-weight:bold;
}
#calendar .maincalendar .calendar-controls .current {
  font-weight: bold;
}


/***
 *** Course
 ***/
#course-view .section {
  font-size:0.95em;
  line-height:1.2em;
}

#course-view .section .activity {
  padding:0.2em 0;
}

#course-view .section .activity a {
  line-height:1em;
}

#course-view .section .left {
  font-weight:bold;
}

.activitydate, .activityhead {
  font-size:0.9em;
}

.weeklydatetext {
  font-size:0.9em;
  font-weight:bold;
}

.coursebox .info {
  font-size:1em;
}

.coursebox .teachers,
.coursebox .cost {
  font-size:0.9em;
}

.coursebox .summary {
  font-size:0.9em;
}

#course-recent h2.main {
  font-size:1.1em;
}




/***
 *** Doc
 ***/
body#doc-contents h1 {
  font-size: 0.9em;
}
body#doc-contents ul {
  font-size: 0.8em;
}


/***
 *** Grades
 ***/

body#grade-index .grades .header {
  font-weight: bold;
  font-size: 0.7em;
}


/***
 *** Login
 ***/

#login-index .content {
  font-size: 0.85em;
}


/***
 *** Logs
 ***/

.logtable td {
  font-size: 0.8em;
}
.logtable th {
  font-size: 0.9em;
}


/***
 *** Message
 ***/

.message .link {
  font-size:0.8em;
}

.message_form {
  font-size:0.8em;
}

.message .heading {
  font-size:1.0em;
  font-weight:bold;
}
.designedby{
	font-size:10px;
}
.message .date,
.message .contact,
.message .summary {
  font-size:0.9em;
}

.message .note, 
.message .pix {
  font-size:0.8em;
}

.message .author {
  font-weight: bold;
  font-size:0.8em;
}

.message .time {
  font-style: italic;
  font-size:0.8em;
}

.message .content {
  font-size:0.8em;
}

#message-user .commands span {
  font-size:0.7em;
  white-space:nowrap;
}

#message-user .name {
  font-weight: bold;
  font-size:1.1em;
}


/***
 *** Tabs
 ***/
.tablink {
  font-size:0.8em;
}

.tablink a:hover {
  text-decoration: none;
}


/***
 *** User
 ***/

.userinfobox .username {
  font-weight: bold;
}

.userinfobox .links {
  font-size: 0.7em;
}


/***
 *** Modules: Assignment
 ***/

#mod-assignment-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Chat
 ***/

#mod-chat-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Choice
 ***/

#mod-choice-index .cell {
  font-size:0.8em;
}
  
/***
 *** Modules: Forum
 ***/

.forumnodiscuss{
  font-weight:bold;
}
.forumpost .topic .subject {
  font-weight: bold;
}
.forumpost .topic .author {
  font-size: 0.8em;
}
.forumpost .commands,
.forumpost .link {
  font-size: 0.9em;
}
.forumheaderlist .discussion .lastpost {
  font-size: 0.9em;
}
body#mod-forum-search .introcontent {
  font-weight:bold;
}
body#mod-forum-index .generalbox .cell {
  font-size: 0.9em;
}



/***
 *** Modules: Glossary
 ***/

.glossarypost .commands {
  font-size: 0.8em;
}
.glossarypost .entryheader .author,
.glossarypost .entryheader .time {
  font-size: 0.8em;
}
.glossarypost .entryheader .time {
  font-style: italic;
}
.concept {
  font-weight: bold;
}
.glossarycomment .time {
  font-size: 0.8em;
  font-style: italic;
}
.entrylowersection .aliases {
  font-size: 0.8em;
}
.entrylowersection .icons,
.entrylowersection .ratings {
  font-size: 0.8em;
}

#mod-glossary-index .cell {
  font-size:0.8em;
}


/***
 *** Modules: Journal
 ***/
#mod-journal-view .lastedit,
#mod-journal-view .editend {
  font-size: 0.7em;
}
#mod-journal-view .author {
  font-size: 1em;
  font-weight: bold;
}
#mod-journal-view .time {
  font-size: 0.7em;
  font-style: italic;
}
#mod-journal-view .grade {
  font-weight: bold;
  font-style: italic;
}

#mod-journal-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Label
 ***/

/***
 *** Modules: Lesson
 ***/

#mod-lesson-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Quiz
 ***/

.editorhelptext {
  font-size:0.7em;
}

#mod-quiz-index .cell {
  font-size:0.8em;
}


/***
 *** Modules: Resource
 ***/

#mod-resource-index .cell {
  font-size:0.8em;
}


/***
 *** Modules: Scorm
 ***/

#mod-scorm-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Survey
 ***/

#mod-survey-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Wiki
 ***/

#mod-wiki-index .cell {
  font-size:0.8em;
}

/***
 *** Modules: Workshop
 ***/

#mod-workshop-index .cell {
  font-size:0.8em;
}

/***** college15_fixed/styles_fonts.css end *****/

/***** college15_fixed/styles_color.css start *****/

/*******************************************************************
 styles_color.css
  
 This CSS file contains all color definitions like 
 background-color, font-color, border-color etc.

 Styles are organised into the following sections:

  core
  header
  footer

  admin
  blocks
  calendar
  course
  doc
  login
  message
  tabs
  user

  various modules

*******************************************************************/

/***
 ***  Core
 ***/

a:link,
a:visited {
  color:#4141A6;
}

a.dimmed:link,
a.dimmed:visited {
  color:#AAAAAA;
}

a:hover {
  color:#FF0000;
}

a.autolink:link,
a.autolink:visited {
  color:#000000;
  background: #DDDDDD;
}

a.autolink.glossary:hover {
  cursor: help;
}


body {
	background-color:#FAFAFA;
}

th.header,
td.header,
div.header {
  border-color:#DDDDDD;
}

.navbar {
	background-color:;
	border-color:#DDDDDD;
}

table.formtable tbody th {
  background: none;
}

.highlight {
  background-color:#AAFFAA;
}

.highlight2 {
  color:#AA0000; /* highlight missing terms in forum search */
}

/* Alternate rows even */
.r0 {  
}

/* Alternate rows odd */
.r1 {  
}

/* notification messages (can be good or bad) */
.notifyproblem {
  color:#660000;
}
.notifysuccess {
  color:#006600;
}

.required {
  background-color:#DDDDDD;
}

.generalbox {
  border-color:#DDDDDD; 
}
.informationbox {
  border-color:#DDDDDD; 
}
.feedbackbox {
  border-color: #888888; 
}
.feedbackby {
  background-color:#BBBBBB;
}

.noticebox {
  border-color:#DDDDDD; 
}

.errorbox {
  color:#ffffff;
  border-color:#660000;
  background-color:#990000;
}

.tabledivider {
  border-color:#DDDDDD;
}

.sitetopic {
}

.sitetopiccontent {
  border-color:#DDDDDD;
  background-color:#FFFFFF;
}

.dimmed_text {
  color:#AAAAAA;
}

.teacheronly {
  color:#990000;
}

.unread {
  background: #6382C2;
} 

.censoredtext {
  color:#000000;
  background:#000000;
}


/* kept for backward compatibility with some non-standard modules
   which use these classes for various things */
.generaltab, .generaltabinactive {
  background-color:#BBBBBB;
}
.generaltabselected {
  background-color:#DDDDDD;
}
.generaltabinactive {
  color:#CCCCCC;
}



/***
 *** Header
 ***/

/***
 *** Footer
 ***/

.homelink a:link,
.homelink a:visited,
.homelink a:hover {
  color: #000;
  text-decoration: none;
}
.homelink a:link,
.homelink a:visited {
  border-top: 1px solid #cecece;
  border-bottom: 2px solid #4a4a4a;
  border-left: 1px solid #cecece;
  border-right: 2px solid #4a4a4a;
}
.homelink a:hover {
  border-bottom: 1px solid #cecece;
  border-top: 2px solid #4a4a4a;
  border-right: 1px solid #cecece;
  border-left: 2px solid #4a4a4a;
}


/***
 *** Admin
 ***/

.admin .generalboxcontent {
  background-color:#EEEEEE; 
}

.generalboxcontent {
	background-color:#EEEEEE;
}
.left{
	background-color:#eeeeee;
}

th.header{
	background-color:#B2C3DB;
}


.right{
	background-color:#eeeeee;
}

.admin .generalbox {
  border-color:#BBBBBB; 
}

.admin .informationbox {
  border-color:#BBBBBB; 
  background-color:#FFFFFF; 
}

body#admin-index .c0 {
  background-color: #FAFAFA;
}



/***
 *** Blocks
 ***/

.sideblock .header {
  border-color: #dddddd;
}

.sideblock .content {
  border-color: #dddddd;
  background-color:#FCFCFC;
}

.sideblock .content hr {
  border-top-color:#999999;
}

#left-column .hidden .header,
#right-column .hidden .header
{
  border-bottom-color: #dddddd;
}

.sideblock .header .hide-show img.hide-show-image {
  background: url('../../pix/t/switch_minus.gif') no-repeat bottom;
}

.sideblock.hidden .header .hide-show img.hide-show-image {
  background: url('../../pix/t/switch_plus.gif') no-repeat bottom;
}



/***
 *** Calendar
 ***/

#calendar .maincalendar,
#calendar .sidecalendar {
  border-color: #DDDDDD;
}

#calendar .maincalendar table.calendarmonth th {
  border-color: #000000;
}

table.minicalendar {
  border-color:#DDDDDD;
}

#calendar .maincalendar .eventlist .event {
  border-color:#DDDDDD;
}

#calendar .maincalendar .eventlist .event .topic,
#calendar .maincalendar .eventlist .event .picture,
#calendar .maincalendar .eventlist .event .side {
  background-color:#EEEEEE;
}

#calendar .maincalendar table.calendarmonth ul.events-underway {
  color:#999999;
}

#calendar .event_global,
.minicalendar .event_global,
.block_calendar_month .event_global {
  border-color:#2EBA0E !important;
  background-color:#2EBA0E;
}

#calendar .event_course,
.minicalendar .event_course,
.block_calendar_month .event_course {
  border-color:#FF9966 !important;
  background-color:#FF9966;
}

#calendar .event_group,
.minicalendar .event_group,
.block_calendar_month .event_group {
  border-color:#FBBB23 !important;
  background-color:#FBBB23;
}

#calendar .event_user,
.minicalendar .event_user,
.block_calendar_month .event_user {
  border-color:#A1BECB !important;
  background-color:#A1BECB;
}

#calendar .duration_global,
.minicalendar .duration_global {
  border-top-color:#2EBA0E !important;
  border-bottom-color:#2EBA0E !important;
}

#calendar .duration_course,
.minicalendar .duration_course {
  border-top-color:#FF9966 !important;
  border-bottom-color:#FF9966 !important;
}

#calendar .duration_group,
.minicalendar .duration_group {
  border-top-color:#FBBB23 !important;
  border-bottom-color:#FBBB23 !important;
}

#calendar .duration_user,
.minicalendar .duration_user {
  border-top-color:#A1BECB !important;
  border-bottom-color:#A1BECB !important;
}

#calendar .weekend,
.minicalendar .weekend {
  color:#FF0000;
}

#calendar .today,
.minicalendar .today {
  border-color:#000000 !important;
}

.cal_popup_fg {
  background-color:#FFFFFF;
}

.cal_popup_bg {
  border-color:#000000;
  background-color:#FFFFFF;
}

#calendar .maincalendar .filters table,
#calendar .sidecalendar .filters table,
.block_calendar_month .filters table {
  background-color: #EEEEEE;
}



/***
 *** Course
 ***/

/* course, entry-page, login */
.headingblock {
  border-color:#DDDDDD;
}

/* course */
.headingblock .outline {
  border-color:#DDDDDD;
}

#course-view .section td {
  border-color:#DDDDDD;
}

#course-view .section .content {
}

#course-view .section .side {
}

#course-view .section .left {
}

#course-view .section .right {
}

#course-view .current .side{
  background: #6382C2;
}

#course-view .topics {
}

#course-view .weeks {
}

#course-view .section .spacer {
}

#course-view .section .weekdates {
  color:#AAAAAA;
}

.categoryboxcontent,
.courseboxcontent {
  border-color:#DDDDDD;
}
body#course-user .section {
  border-color:#AAAAAA;
}



/***
 *** Doc
 ***/

/***
 *** Grades
 ***/

body#grade-index .grades {
  border-color:black;
}

body#grade-index .grades td {
  border-color:#e0e0e0;
}

body#grade-index .grades .r0 {
  background-color: #ffffff;
}

body#grade-index .grades .r1 {
  background-color: #f0f0f0;
}


/***
 *** Login
 ***/

.loginbox .content {
  border-color:#DDDDDD;
}


/***
 *** Message
 ***/

table.message_search_results td {
  border-color:#DDDDDD;
}

.message.other .author {
  color: #8888CC;
}

.message.me .author {
  color: #999999;
}

.message .time {
  color: #999999;
}

.message .content {
}

/***
 *** Logs
 ***/

.logtable .r1 {
  background-color:#EEEEEE;
}


/***
 *** Tabs
 ***/

.tablink a:link,
.tablink a:visited {
  color:#000066;
}

.selected .tablink a:link,
.selected .tablink a:visited {
  color:#000000;
}
.tabs .side,
.tabrow td {
  border-color: #AAAAAA;
}
.tabrow td {
  background:url(pix/tab/left.gif) top left no-repeat;
}
.tabrow td .tablink {
  background:url(pix/tab/right.gif) top right no-repeat;
}
.tabrow td:hover {
  background-image:url(pix/tab/left_hover.gif);
}
.tabrow td:hover .tablink {
  background-image:url(pix/tab/right_hover.gif);
}
.tabrow .last {
  background: transparent url(pix/tab/right_end.gif) top right no-repeat;
}
.tabrow .selected {
  background:url(pix/tab/left_active.gif) top left no-repeat;
}
.tabrow .selected .tablink {
  background:url(pix/tab/right_active.gif) top right no-repeat;
}
.tabrow td.selected:hover {
  background-image:url(pix/tab/left_active_hover.gif);
}
.tabrow td.selected:hover .tablink {
  background-image:url(pix/tab/right_active_hover.gif);
}


/***
 *** User
 ***/

.userpicture {
}

.userinfobox {
  border-color: #DDDDDD;
}
.groupinfobox {
  border-color: #DDDDDD;
}


/***
 *** Modules: Chat
 ***/

/***
 *** Modules: Choice
 ***/

/***
 *** Modules: Forum
 ***/

.forumheaderlist,
.forumpost {
	border-color:#DDDDDD;
}

.forumpost .content {
  background: #FFFFFF;
}

.forumpost .left {
  background-color:#B2C3DB; 
}

.author{
		background-color:#B2C3DB;
}
.replies{
	background-color:#B2C3DB;
}
.picture{
	background-color:#B2C3DB;
}
.forumpost .topic {
  border-bottom-color: #EEEEEE;
}

.forumpost .starter {
  background:#B2C3DB; 
}

.forumheaderlist .discussion .starter {
  background:#B2C3DB;
}

.forumheaderlist .discussion .lastpost {
	background-color:#B2C3DB;
}

.forumheaderlist td {
  border-color: #FFFFFF;
}

.sideblock .post .head {
  color:#555555;
}

.forumthread .unread {
  background: #6382C2;
}
#mod-forum-discuss .forumpost {
  background: none;
}

#mod-forum-discuss .forumpost.unread .content {
  border-color: #6382C2; 
} 

#mod-forum-discuss .forumthread .unread {
} 

#mod-forum-index .unread {
}


/***
 *** Modules: Glossary
 ***/

.entryboxheader {
  border-color: #BBBBBB;
}

.entrybox {
  border-color: #BBBBBB;
}

.entry {
}

.glossarypost {
  border-color: #DDDDDD;
}

.glossarypost .entryheader,
.glossarypost .entryapproval,
.glossarypost .picture,
.glossarypost .entryattachment,
.glossarypost .left {
  background-color: #F0F0F0;
}

.glossarycomment {
  border-color: #DDDDDD;
}

.glossarycomment .entryheader,
.glossarycomment .picture,
.glossarycomment .left {
  background-color: #F0F0F0;

}

#mod-glossary-report .generalbox .teacher {
  background: #F0F0F0;
}

.categoryheader {
  background-color: #dddddd;
}

.glossaryformatheader {
  background-color: #dddddd;
}


/***
 *** Modules: Journal
 ***/

#mod-journal-view .feedbackbox .left,
#mod-journal-view .feedbackbox .entryheader {
  background-color: #dddddd;
}

/***
 *** Modules: Label
 ***/

/***
 *** Modules: Lesson
 ***/

/***
 *** Modules: Quiz
 ***/

body#mod-quiz-report table#attempts td {
  border-color: #dddddd;
}
body#mod-quiz-report table#attempts .r1 {
  background-color: #eeeeee;
}


/***
 *** Modules: Resource
 ***/

/***
 *** Modules: Scorm
 ***/

/***
 *** Modules: Survey
 ***/

#mod-survey-view .r0 {
  background-color: #EEEEEE;
}
#mod-survey-view .r1 {
  background-color: #DDDDDD;
}


/***
 *** Modules: Wiki
 ***/

/***
 *** Modules: Workshop
 ***/

.workshoppostpicture {
  background-color:#FEE6B9;
}

.workshopassessmentheading {
  background-color:#DDDDDD;
}

/***** college15_fixed/styles_color.css end *****/

