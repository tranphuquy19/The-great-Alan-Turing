/**************************************
 * THEME NAME: standard
 *
 * Files included in this sheet:
 *
 *   standard/styles_layout.css
 *   standard/styles_fonts.css
 *   standard/styles_color.css
 *   /mod/assignment/styles.php
 *   /mod/choice/styles.php
 *   /mod/data/styles.php
 *   /mod/lesson/styles.php
 *   /mod/quiz/styles.php
 *   /mod/quiz1/styles.php
 *   /mod/quiz5/styles.php
 *   /mod/scorm/styles.php
 *   /mod/workshop/styles.php
 *   /blocks/admin/styles.php
 *   /blocks/calendar_month/styles.php
 *   /blocks/calendar_upcoming/styles.php
 *   /blocks/course_summary/styles.php
 *   /blocks/login/styles.php
 *   /blocks/quiz_results/styles.php
 *   /blocks/rss_client/styles.php
 *   /blocks/search_forums/styles.php
 **************************************/

/***** standard/styles_layout.css start *****/

/*******************************************************************
 styles_layout.css
  
 This CSS file contains all layout definitions like positioning,
 floats, margins, padding, borders etc.

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
}

#layout-table #left-column,
#layout-table #middle-column,
#layout-table #right-column {
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

img.userpicture,
img.grouppicture,
.block_online_users .listentry img {
  border: 0px none
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

.errorboxcontent {
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

table.formtable tbody .htmlarea td,
table.formtable tbody .htmlarea th
{
  padding: 0px;
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

.headermain {
  float:left;
}

.headermenu {
  float:right;
  text-align:right;
}

.navbar {
  width:100%;
  padding:3px 0.5em;
  height:1.3em;
  border-width:1px;
  border-style:solid;
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
 *** Content
 ***/

#content {
  margin-top:8px;
}

#admin-index #content {
  margin-top:0;
}

/***
 *** Admin
 ***/
 
body#admin-index .c0 {
  vertical-align: top;
} 

body#admin-index .c1 {
  vertical-align: middle;
} 

body#admin-modules table.generaltable td.cell,
body#admin-modules .generaltablecell {
  padding-top: 2px;
  padding-bottom: 2px;
} 

body#admin-blocks table#blocks,
body#admin-blocks table#incompatible {
  width: 70%;
  margin: auto;
}

body#admin-blocks table#blocks th,
body#admin-blocks table#incompatible th,
body#admin-blocks table#blocks td.cell,
body#admin-blocks table#incompatible td.cell {
  padding: 4px;
  text-align: center;
  vertical-align: middle;
} 

body#admin-blocks table#blocks td.c0,
body#admin-blocks table#blocks th.c0,
body#admin-blocks table#incompatible td.c0,
body#admin-blocks table#incompatible th.c0 {
  text-align: left;
}

body#admin-blocks 
body#admin-config .confighelp {
  display: block;
  padding-bottom: 20px;
}

table.flexible td.cell {
  padding-top: 2px;
  padding-bottom: 2px;
} 

table.flexible {
  width: 70%;
  margin: auto;
}

table.flexible thi, 
table.flexible td.cell {
  padding: 4px;
  text-align: center;
  vertical-align: middle;
} 

table.flexible td.c0,
table.flexible th.c0 {
  text-align: left;
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

.sideblock .content .message {
  text-align:center  
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

.blockconfigtable {
  margin-top: 0;
}

.blockconfiginstancecontent .tabs {
  margin-bottom: 0px;
}

.block_online_users .listentry {
  padding-top:5px;
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
  padding: 0px;
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

.minicalendarblock {
  padding: 0px 4px;
}

table.minicalendar {
  width: 100%;
  margin: 10px auto;
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

#calendar .indent {
    padding-left: 20px;
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

* html #course-view .section .content .commands {
  clear: both;
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

.backup-form-instances {
   margin:0px 20px 0px 20px;
}
.restore-form-instances {
   margin:0px 20px 0px 20px;
}

/***
 *** Login
 ***/

.loginbox {
  margin-top:7px;
}

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

body#user-index h2 {
  text-align: center;
}

body#user-index #longtimenosee,
body#user-index #showall {
  text-align: center;
}

body#user-index #showall {
  margin: 10px 0px;
}

body#user-index table#teachers,
body#user-index table#students {
  margin: auto;
  width: 80%;
}
body#user-index table#teachers td,
body#user-index table#teachers th,
body#user-index table#students td,
body#user-index table#students th {
  vertical-align: middle;
  text-align: left;
  padding: 4px;
}

body#user-index table.controls {
  width: 100%;
}
body#user-index table.controls tr {
  vertical-align: top;
}
body#user-index table.controls td.right,
body#user-index table.controls td.left {
  padding: 4px;
}
body#user-index table.controls .right {
  text-align: right;
}
body#course-participation h2 {
  text-align:center;
}
body#course-participation #showall {
  text-align:center;
  margin: 10px 0px;
}

/***
 *** Modules: Assignment
 ***/

/***
 *** Modules: Chat
 ***/

#mod-chat-gui_header_js-jsupdate {
  margin:10px
}
#mod-chat-gui_header_js-jsupdate .chat-event,
#mod-chat-gui_header_js-jsupdate .chat-message {
  width:100%;
  padding:0;
  margin-top:7px
}
#mod-chat-gui_header_js-jsupdate .picture {
  width:40px
}

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

#mod-glossary-comments .glossarypost,
#mod-glossary-comment .glossarypost {
      margin-top: 15px;
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
  text-align:right;
}

body#mod-quiz-report table#attempts,
body#mod-quiz-report table#commands,
body#mod-quiz-report table#itemanalysis
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
  vertical-align: middle;
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

.navbutton form {
  display: inline;
  }

/***
 *** Modules: Resource
 ***/

.ims-nav-bar {
  position: absolute; 
  top: 2px; 
  left: 2px;
}

.ims-nav-button a,
.ims-nav-dimmed {
  padding-left:1em;
  padding-right:1em;
}

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
/***** standard/styles_layout.css end *****/

/***** standard/styles_fonts.css start *****/

/*******************************************************************
 styles_fonts.css
  
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
  font-family:Arial, Verdana, Helvetica, sans-serif;
  font-size:100%;
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

.errorboxcontent {
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

.logininfo,
#header-home .headermenu font {
  font-size:0.8em;
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

body#admin-blocks table#incompatible td.c0 {
  font-weight: bold;
}

body#admin-index .explanation {
  font-size: 0.7em;
  vertical-align: bottom;
}

body#admin-index .copyright {
  text-align: center;
  font-size: 0.8em;
}

.environmenttable {
  font-size: 0.8em;
}

/***
 *** Blocks
 ***/

.sideblock .header {
  font-size:0.9em;
  font-weight: bold;
}

.sideblock .content {
  font-size:0.9em;
  line-height:1.2em;
}

.sideblock a {
  line-height:1.2em
}

.sideblock .content h3,
.sideblock .content h2 {
  font-size:1.0em;
}

.sideblock .content .message {
  font-size:0.9em
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

.block_online_users .listentry {
  text-align:left;
  font-size:0.75em
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

body#user-index #longtimenosee {
  font-size: 0.8em;
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
.forumpost .link,
.forumpost .footer {
  font-size: 0.9em;
}
.forumheaderlist .discussion .lastpost {
  font-size: 0.7em;
}
body#mod-forum-search .introcontent {
  font-weight:bold;
}
body#mod-forum-index .generalbox .cell {
  font-size: 0.80em;
}

.forumpost .edited {
  font-style: italic;
}


/***
 *** Modules: Glossary
 ***/

.glossarypost .commands {
  font-size: 0.8em;
}
.glossarypost .author {
  font-size: 0.8em;
}
.glossarypost .time {
  font-size: 0.8em;
}
.concept {
  font-weight: bold;
}
.glossarycomment .author {
  font-size: 0.8em;
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

.ims-nav-dimmed,
.ims-nav-button {
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

/***** standard/styles_fonts.css end *****/

/***** standard/styles_color.css start *****/

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
  color:#0000FF;
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

img.userpicture,
img.grouppicture {
  border-color:#000
}

.block_online_users .listentry img {
  border:#888
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

.errorboxcontent {
  background-color:#FFBBBB;
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
  background: #FFD991;
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

body#admin-blocks table#blocks .r0,
body#admin-blocks table#incompatible .r0 {
  background-color: #f0f0f0;
}

body#admin-blocks table#blocks .r1,
body#admin-blocks table#incompatible .r1 {
  background-color: #fafafa;
}

body#admin-blocks table#incompatible td.c0 {
  color: #ff0000;
}

table.flexible  .r0 {
  background-color: #f0f0f0;
}

table.flexible .r1 {
  background-color: #fafafa;
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

.blockconfigtable {
  background-color:#FFFFFF;
  border-left:1px solid;
  border-right:1px solid;
  border-bottom:1px solid;
  border-color:#AAAAAA;
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
  border-color: #DDDDDD;
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
  background: #FFD991;
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

#mod-chat-gui_header_js-jsupdate .text {
  color:#000
}
#mod-chat-gui_header_js-jsupdate .event,
#mod-chat-gui_header_js-jsupdate .title {
  color:#888
}

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
  background:#EEEEEE; 
}

.forumpost .topic {
  border-bottom-color: #EEEEEE;
}

.forumpost .starter {
  background:#DDDDDD; 
}

.forumheaderlist .discussion .starter {
  background:#DDDDDD; 
}

.forumheaderlist td {
  border-color: #FFFFFF;
}

.sideblock .post .head {
  color:#555555;
}

.forumthread .unread {
  background: #FFD991;
}
#mod-forum-discuss .forumpost {
  background: none;
}

#mod-forum-discuss .forumpost.unread .content {
  border-color: #FFD991; 
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

.ims-nav-dimmed {
  color: #AAAAAA;
  text-decoration: none;
}

.ims-nav-button a:link,
.ims-nav-button a:visited,
.ims-nav-button a:hover {
  color: #000;
  text-decoration: none;
}

.ims-nav-dimmed,
.ims-nav-button a:link,
.ims-nav-button a:visited {
  border-top: 1px solid #cecece;
  border-bottom: 2px solid #4a4a4a;
  border-left: 1px solid #cecece;
  border-right: 2px solid #4a4a4a;
}

.ims-nav-button a:hover {
  border-bottom: 1px solid #cecece;
  border-top: 2px solid #4a4a4a;
  border-right: 1px solid #cecece;
  border-left: 2px solid #4a4a4a;
}


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

.error {
  color:#ff0000;
}
/***** standard/styles_color.css end *****/

/***** /mod/assignment/styles.php start *****/

#mod-assignment-submissions .feedback .content,
#mod-assignment-submissions .feedback .topic,
#mod-assignment-submissions .feedback .picture
{
  padding: 10px;
  border-width:1px;
  border-style:solid;
  border-color:#DDDDDD;
}

.mod-assignment .feedback .files {
  float: right;
  background-color: #EFEFEF;
  padding:5px;
}

.mod-assignment .feedback .grade {
  float: right;
}

.mod-assignment .feedback .from {
  float: left;
}

.mod-assignment .feedback .time {
  font-size: 0.8em;
}

.mod-assignment .late {
  color: red;
}

.mod-assignment .files img {
  margin-right: 4px;
}

.mod-assignment .files a {
  white-space:nowrap;
}

#mod-assignment-submissions .generaltable .r1 {
  background-color: #FFFFFF;
}

#mod-assignment-submissions .header .commands {
  display: inline;
}

#mod-assignment-submissions .s0 {
  background: #FFD991;
}

#mod-assignment-submissions table.submissions td,
#mod-assignment-submissions table.submissions th
{
  border-width: 1px;
  border-style: solid;
  border-color: #DDDDDD;
  vertical-align: middle;
  padding-left: 5px;
  padding-right: 5px;
}

#mod-assignment-submissions .submissions .grade {
  text-align: right;
  font-weight:bold;
}

#mod-assignment-submissions .picture {
  width: 35px;
}

#mod-assignment-submissions .fullname {
  text-align: left;
}

#mod-assignment-submissions .timemodified,
#mod-assignment-submissions .timemarked
{
  text-align: left;
  font-size: 0.9em;
}

#mod-assignment-submissions .status {
  text-align: center;
}

#mod-assignment-view #online .singlebutton {
  text-align: center;
}

#mod-assignment-view #dates {
  font-size: 0.8em;
  margin-top: 30px;
  margin-bottom: 30px;
}

#mod-assignment-view #dates .c0{
  text-align:right;
  font-weight:bold;
}

#mod-assignment-view .feedback {
  border-width:1px;
  border-style:solid;
  border-color:#DDDDDD;
  margin-top: 15px;
  width: 80%;
  margin-left: 10%;
  margin-right: 10%;
}

#mod-assignment-view .feedback .topic {
  padding: 4px;
  border-style:solid;
  border-width: 0px;
  border-bottom-width: 1px;
  border-color:#DDDDDD;
}

#mod-assignment-view .feedback .fullname {
  font-weight: bold;
}

#mod-assignment-view .feedback .date {
  font-size: 0.8em;
}

#mod-assignment-view .feedback .content {
  padding: 4px;
}

#mod-assignment-view .feedback .grade {
  text-align: right;
  font-weight:bold;
}

#mod-assignment-view .feedback .left {
  width: 35px;
  padding: 4px;
  text-align: center;
  vertical-align: top;
}
/***** /mod/assignment/styles.php end *****/

/***** /mod/choice/styles.php start *****/

.mod-choice .results {
  border-collapse: separate;
}

.mod-choice .results .data {
  border-width:1px;
  border-style:solid;
  border-color:#999;
}
/***** /mod/choice/styles.php end *****/

/***** /mod/data/styles.php start *****/

#mod-data-view #sortsearch .c0 {
  text-align: right;
}
/***** /mod/data/styles.php end *****/

/***** /mod/lesson/styles.php start *****/

/***
 *** Style for page contents (display to student)
 ***/
 
.mod-lesson .contents {
    text-align: left;
}

/***
 *** Slide show Style
 ***/

/* NOTE: background color, height and width are set in the lesson settings */
.mod-lesson .slideshow {  
    overflow: auto;
    padding-right: 16px; /* for the benefit of macIE5 only */ 
    /* \ commented backslash hack - recover from macIE5 workarounds, it will ignore the following rule */
    padding-right: 0;
    padding: 15px;
}

/***
 *** Hide Label Class
 ***/

.mod-lesson .hidden-label {
  display: none;
}

/***
 *** Left Menu Styles
 ***/

.mod-lesson .leftmenu_container {
  width:170px;
  height:400px;
  overflow:auto;
  vertical-align:top;
  padding-bottom: 15px;  /* for the sake of MacIE5 only */
}
.mod-lesson .leftmenu_title {
}
.mod-lesson .leftmenu_courselink {
    font-size:.9em;
}
.mod-lesson .leftmenu_links {
    font-size:.85em;
    font-style: none;
}
.mod-lesson .leftmenu_links ul {
    list-style-type: none;
    margin: 0px;
    padding: 0px;
    padding-top: 5px;
    padding-left: 10px;
}

.mod-lesson .leftmenu_selected_link {
    
}

.mod-lesson .leftmenu_not_selected_link {
    
}

.mod-lesson .skip {
    position: absolute;
    left: -1000em;
    width: 20em;
}


/***
 *** Lesson Buttons
 ***/

.mod-lesson .lessonbutton a {
  padding-left:1em;
  padding-right:1em;
}

.mod-lesson .lessonbutton a:link,
.mod-lesson .lessonbutton a:visited, 
.mod-lesson .lessonbutton a:hover {
    color: #000;
    text-decoration: none;
}

.mod-lesson .lessonbutton a:link,
.mod-lesson .lessonbutton a:visited {
  border-top: 1px solid #cecece;
  border-bottom: 2px solid #4a4a4a;
  border-left: 1px solid #cecece;
  border-right: 2px solid #4a4a4a;
}

.mod-lesson .lessonbutton a:hover {
  border-bottom: 1px solid #cecece;
  border-top: 2px solid #4a4a4a;
  border-right: 1px solid #cecece;
  border-left: 2px solid #4a4a4a;
}


/***
 ***  Use these to override lessonbutton class
 ***  Or just comment out all of lessonbutton class definitions and start from scratch below
 ***/

/* for branch tables only */
.mod-lesson .previousbutton {
}

/* for branch tables only */
.mod-lesson .nextbutton {
}

/* All other buttons */
.mod-lesson .standardbutton {
}

/*  branchbuttoncontainer wraps around branch table buttons */
.mod-lesson .branchbuttoncontainer {
    text-align: center;
}

/*  branchslidetop and branchslidebottom classes are wrapped around the branch buttons (branchslidetop around 
    top ones and branchslidebottom around the bottom ones)
    that are printed out with the branch table in slide show mode. */
.mod-lesson .branchslidetop {
    /*  You could float them out of the slide
    position: absolute;
    top: 60px;*/
    /*  You may choose to not show them at all
    display: none;*/
}

.mod-lesson .branchslidebottom {
    /*  You may choose to not show them at all 
    display: none; */
}

/***
 *** Lesson Progress Bar
 ***    Default styles for this are very basic right now.
 ***    User is supposed to configure this to their liking (like using pictures)
 ***/

.mod-lesson .progress_bar {
    padding: 20px;
}

.mod-lesson .progress_bar_table {
    width: 80%;
    padding: 0px;
    margin: 0px;
}

.mod-lesson .progress_bar_completed {
    /*  Example Use of Image
    background-image: url(http://192.168.1.5/mod/lesson/completed.gif);
    background-position: center;
    background-repeat: repeat-x;
    */
    background-color: green;
    padding: 0px;
    margin: 0px;    
}

.mod-lesson .progress_bar_todo {
    /*  Example Use of Image
    background-image: url(http://192.168.1.5/mod/lesson/todo.gif);
    background-repeat: repeat-x;
    background-position: center;
    */
    background-color: red;
    text-align: left;
    padding: 0px;
    margin: 0px;
}

.mod-lesson .progress_bar_token {
    /*  Example Use of Image
    background-image: url(http://192.168.1.5/mod/lesson/token.gif);
    background-repeat: repeat-none;
    */
    background-color: #000000;
    height: 20px;
    width: 5px;
    padding: 0px;
    margin: 0px;
}/***** /mod/lesson/styles.php end *****/

/***** /mod/quiz/styles.php start *****/



.mod-quiz .quiz-report-title {
  text-align: center;
  font-weight : bold;
}
.mod-quiz .grade {
  font-size: small;
  margin-top: 10pt
}
.mod-quiz .gradingdetails {
  font-size: small;
}


body#mod-quiz-report table#itemanalysis {
  margin: 20px auto;
}
body#mod-quiz-report table#itemanalysis .header,
body#mod-quiz-report table#itemanalysis .cell
{
  padding: 4px;
}
body#mod-quiz-report table#itemanalysis .header .commands {
  display: inline;
}
body#mod-quiz-report table#itemanalysis td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#itemanalysis .header {
  text-align: left;
}
body#mod-quiz-report table#itemanalysis .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#itemanalysis .uncorrect {
  color: red;
}

body#mod-quiz-report table#itemanalysis .correct {
  color: blue;
  font-weight : bold;
}

body#mod-quiz-report table#itemanalysis .partialcorrect {
  color: green !important;
}

body#mod-quiz-report table#itemanalysis .qname {
  color: green !important;
}

/* manual grading */
body#mod-quiz-grading table#grading
{
  width: 80%;
  margin: auto;
}
body#mod-quiz-grading table#grading
{
  margin: 20px auto;
}
body#mod-quiz-grading table#grading .header,
body#mod-quiz-grading table#grading .cell
{
  padding: 4px;
}
body#mod-quiz-grading table#grading .header .commands 
{
  display: inline;
}
body#mod-quiz-grading table#grading .picture 
{
  width: 40px;
}
body#mod-quiz-grading table#grading td 
{
  border-left-width: 1px;
  border-right-width: 1px;
  border-left-style: solid;
  border-right-style: solid;
  vertical-align: bottom;
}


body#mod-quiz-grading table#grading .header {
  text-align: left;
}
body#mod-quiz-grading table#grading .picture {
  text-align: center !important;
}
body#mod-quiz-grading .controls {
  text-align: center;
}

body#mod-quiz-grading table#grading td {
  border-color: #dddddd;
}
body#mod-quiz-grading table#grading .r1 {
  background-color: #eeeeee;
}
/* grading */



body#mod-quiz-report table#responses {
  margin: 20px auto;
}
body#mod-quiz-report table#responses .header,
body#mod-quiz-report table#responses .cell
{
  padding: 4px;
}
body#mod-quiz-report table#responses .header .commands {
  display: inline;
}
body#mod-quiz-report table#responses td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#responses .header {
  text-align: left;
}
body#mod-quiz-report table#responses .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#responses .uncorrect {
  color: red;
}

body#mod-quiz-report table#responses .correct {
  color: green;
}

body#mod-quiz-report table#responses .partialcorrect {
  color: orange;
}

#mod-quiz-attempt #timer .generalbox {
  width:150px
}

#mod-quiz-attempt #timer {
  position:absolute;
  /*top:100px; is set by js*/
  left:10px
}

.mod-quiz #categoryquestions td {
  white-space:nowrap;
}
/***** /mod/quiz/styles.php end *****/

/***** /mod/quiz1/styles.php start *****/



.mod-quiz .quiz-report-title {
  text-align: center;
  font-weight : bold;
}
.mod-quiz .grade {
  font-size: small;
  margin-top: 10pt
}
.mod-quiz .gradingdetails {
  font-size: small;
}


body#mod-quiz-report table#itemanalysis {
  margin: 20px auto;
}
body#mod-quiz-report table#itemanalysis .header,
body#mod-quiz-report table#itemanalysis .cell
{
  padding: 4px;
}
body#mod-quiz-report table#itemanalysis .header .commands {
  display: inline;
}
body#mod-quiz-report table#itemanalysis td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#itemanalysis .header {
  text-align: left;
}
body#mod-quiz-report table#itemanalysis .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#itemanalysis .uncorrect {
  color: red;
}

body#mod-quiz-report table#itemanalysis .correct {
  color: blue;
  font-weight : bold;
}

body#mod-quiz-report table#itemanalysis .partialcorrect {
  color: green !important;
}

body#mod-quiz-report table#itemanalysis .qname {
  color: green !important;
}

/* manual grading */
body#mod-quiz-grading table#grading
{
  width: 80%;
  margin: auto;
}
body#mod-quiz-grading table#grading
{
  margin: 20px auto;
}
body#mod-quiz-grading table#grading .header,
body#mod-quiz-grading table#grading .cell
{
  padding: 4px;
}
body#mod-quiz-grading table#grading .header .commands 
{
  display: inline;
}
body#mod-quiz-grading table#grading .picture 
{
  width: 40px;
}
body#mod-quiz-grading table#grading td 
{
  border-left-width: 1px;
  border-right-width: 1px;
  border-left-style: solid;
  border-right-style: solid;
  vertical-align: bottom;
}


body#mod-quiz-grading table#grading .header {
  text-align: left;
}
body#mod-quiz-grading table#grading .picture {
  text-align: center !important;
}
body#mod-quiz-grading .controls {
  text-align: center;
}

body#mod-quiz-grading table#grading td {
  border-color: #dddddd;
}
body#mod-quiz-grading table#grading .r1 {
  background-color: #eeeeee;
}
/* grading */



body#mod-quiz-report table#responses {
  margin: 20px auto;
}
body#mod-quiz-report table#responses .header,
body#mod-quiz-report table#responses .cell
{
  padding: 4px;
}
body#mod-quiz-report table#responses .header .commands {
  display: inline;
}
body#mod-quiz-report table#responses td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#responses .header {
  text-align: left;
}
body#mod-quiz-report table#responses .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#responses .uncorrect {
  color: red;
}

body#mod-quiz-report table#responses .correct {
  color: green;
}

body#mod-quiz-report table#responses .partialcorrect {
  color: orange;
}

#mod-quiz-attempt #timer .generalbox {
  width:150px
}

#mod-quiz-attempt #timer {
  position:absolute;
  /*top:100px; is set by js*/
  left:10px
}

.mod-quiz #categoryquestions td {
  white-space:nowrap;
}
/***** /mod/quiz1/styles.php end *****/

/***** /mod/quiz5/styles.php start *****/



.mod-quiz .quiz-report-title {
  text-align: center;
  font-weight : bold;
}
.mod-quiz .grade {
  font-size: small;
  margin-top: 10pt
}
.mod-quiz .gradingdetails {
  font-size: small;
}


body#mod-quiz-report table#itemanalysis {
  margin: 20px auto;
}
body#mod-quiz-report table#itemanalysis .header,
body#mod-quiz-report table#itemanalysis .cell
{
  padding: 4px;
}
body#mod-quiz-report table#itemanalysis .header .commands {
  display: inline;
}
body#mod-quiz-report table#itemanalysis td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#itemanalysis .header {
  text-align: left;
}
body#mod-quiz-report table#itemanalysis .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#itemanalysis .uncorrect {
  color: red;
}

body#mod-quiz-report table#itemanalysis .correct {
  color: blue;
  font-weight : bold;
}

body#mod-quiz-report table#itemanalysis .partialcorrect {
  color: green !important;
}

body#mod-quiz-report table#itemanalysis .qname {
  color: green !important;
}

/* manual grading */
body#mod-quiz-grading table#grading
{
  width: 80%;
  margin: auto;
}
body#mod-quiz-grading table#grading
{
  margin: 20px auto;
}
body#mod-quiz-grading table#grading .header,
body#mod-quiz-grading table#grading .cell
{
  padding: 4px;
}
body#mod-quiz-grading table#grading .header .commands 
{
  display: inline;
}
body#mod-quiz-grading table#grading .picture 
{
  width: 40px;
}
body#mod-quiz-grading table#grading td 
{
  border-left-width: 1px;
  border-right-width: 1px;
  border-left-style: solid;
  border-right-style: solid;
  vertical-align: bottom;
}


body#mod-quiz-grading table#grading .header {
  text-align: left;
}
body#mod-quiz-grading table#grading .picture {
  text-align: center !important;
}
body#mod-quiz-grading .controls {
  text-align: center;
}

body#mod-quiz-grading table#grading td {
  border-color: #dddddd;
}
body#mod-quiz-grading table#grading .r1 {
  background-color: #eeeeee;
}
/* grading */



body#mod-quiz-report table#responses {
  margin: 20px auto;
}
body#mod-quiz-report table#responses .header,
body#mod-quiz-report table#responses .cell
{
  padding: 4px;
}
body#mod-quiz-report table#responses .header .commands {
  display: inline;
}
body#mod-quiz-report table#responses td {
  border-width: 1px;
  border-style: solid;
}
body#mod-quiz-report table#responses .header {
  text-align: left;
}
body#mod-quiz-report table#responses .numcol {
  text-align: center;
  vertical-align : middle !important;
}

body#mod-quiz-report table#responses .uncorrect {
  color: red;
}

body#mod-quiz-report table#responses .correct {
  color: green;
}

body#mod-quiz-report table#responses .partialcorrect {
  color: orange;
}

#mod-quiz-attempt #timer .generalbox {
  width:150px
}

#mod-quiz-attempt #timer {
  position:absolute;
  /*top:100px; is set by js*/
  left:10px
}

.mod-quiz #categoryquestions td {
  white-space:nowrap;
}
/***** /mod/quiz5/styles.php end *****/

/***** /mod/scorm/styles.php start *****/

.structlist  {
  list-style-type: none;
  white-space: nowrap;
  font-size: small;
}
.orgtitle {
  font-weight: bold;
  font-size: small;
}
.mod-scorm .top {
  vertical-align: top;
}
.mod-scorm .left {
  text-align: left;
}
.mod-scorm .center {
  text-align: center;
}
.mod-scorm .right {
  text-align: right;
}
.mod-scorm .scoframe {

}

#mod-scorm-player #scormpage {
  position: relative;
  width: 100%;
}
#mod-scorm-player #tocbox {
  position: absolute;
  left: 0px;
  top: 0px;
  width: 19%;
}
#mod-scorm-player #tochead {
  text-align: center;
  font-weight: bold;
}
#mod-scorm-player #scormbox {
  position: absolute;
  right: 0px;
  top: 0px;
}
#mod-scorm-player .toc {
  width: 80%; 
  margin-left: 20%; 
}
#mod-scorm-player .no-toc {
  width: 100%;
}
#mod-scorm-player #scormobject {
 /* border: 1px solid black; */
}
#mod-scorm-player #scormtop {
  position: relative;
  width: 100%;
  height: 30px;
}
#mod-scorm-player #scormbrowse {
  position: absolute;
  left: 5px;
  top: 0px;
}
#mod-scorm-player #scormnav {
  position: absolute;
  right: 5px;
  top: 0px;
}
#mod-scorm-player .structurelist {
  list-style-type: none;
  text-indent:-4ex;
  font-size: small;
}

#mod-scorm-view .structurehead {
  font-weight: bold;
  text-align: center;
}
#mod-scorm-view .structurelist  {
  list-style-type: none;
  white-space: nowrap;
}
/***** /mod/scorm/styles.php end *****/

/***** /mod/workshop/styles.php start *****/

.workshop_feedbackbox {
    margin-top: 5px;
    border-width: 1px;
    border-style: solid;
    border-color: #999999;
}

.workshop_feedbackbox .picture {
    vertical-align: top;
}

.workshop_feedbackbox .author {
    vertical-align: top;
    display: block;
}

.workshop_feedbackbox .time {
    vertical-align: top;
    display: block;
}

.workshop_feedbackbox .content {
    vertical-align: top;
}

.workshop_feedbackbox .comment {
    display: block;
}

.workshop_feedbackbox .teachercomment {
    display: block;
    font-weight: bold;
}
/***** /mod/workshop/styles.php end *****/

/***** /blocks/admin/styles.php start *****/

.block_adminblock .content {
    text-align: center;
    padding: 10px;
}
/***** /blocks/admin/styles.php end *****/

/***** /blocks/calendar_month/styles.php start *****/

.block_calendar_month .cal_popup_caption,
.block_calendar_month .cal_popup_fg div {
    font-size: 0.85em !important;
}

.block_calendar_month .filters {
    font-size:0.75em;
    padding: 5px;
}

.block_calendar_month .filters table {
    border-collapse:separate;
    border-spacing: 2px;
    padding: 2px;
}

.block_calendar_month .event_global,
.block_calendar_month .event_course,
.block_calendar_month .event_group,
.block_calendar_month .event_user {
    border-width: 2px;
    border-style: solid;
}
/***** /blocks/calendar_month/styles.php end *****/

/***** /blocks/calendar_upcoming/styles.php start *****/

.block_calendar_upcoming .event .date {
    text-align:right;
}
/***** /blocks/calendar_upcoming/styles.php end *****/

/***** /blocks/course_summary/styles.php start *****/

.block_course_summary .content {
    padding:10px;
}
/***** /blocks/course_summary/styles.php end *****/

/***** /blocks/login/styles.php start *****/

.block_login .logintable {
  text-align:center;
}

.block_login .loginform {
  display:inline;
}
/***** /blocks/login/styles.php end *****/

/***** /blocks/quiz_results/styles.php start *****/

.block_quiz_results {
    text-align: center;
}

.block_quiz_results table.grades .number, 
.block_quiz_results table.grades .grade {
    text-align: right;
    width: 10%;
}

.block_quiz_results table.grades {
    text-align: left;
    width: 100%;
}

.block_quiz_results table.grades caption {
    margin: 1em 0px 0px 0px;
    border-bottom: 1px solid;
    font-weight: bold;
}

.block_quiz_results h1 {
    margin: 4px;
    font-weight: bold;
    font-size: 1.1em;
}
/***** /blocks/quiz_results/styles.php end *****/

/***** /blocks/rss_client/styles.php start *****/

.block_rss_client .link {
  border-top:1px solid;
  border-top-color:#DDDDDD;
  padding-bottom:5px;
  font-size:0.82em;
}

.block_rss_client .description {
  color:#555555;
  font-size:0.78em;
  padding-left:10px;
  padding-bottom:8px;
}

.block_rss_client .title {
  font-size:1.0em;
}

.block_rss_client .image {
}

.blockconfigtable #rssfeeds {
    width: 100%;
}

.blockconfigtable #rssfeeds td.actions {
    text-align: center;
    vertical-align: middle;
    padding: 10px;
}

.blockconfigtable #rssfeeds td.feed {
    vertical-align: middle;
    padding: 5px;
}

.blockconfigtable #rssfeeds .title {
    font-weight: bold;
    margin-bottom: 2px;
}

.blockconfigtable #rssfeeds .url, .blockconfigtable #rssfeeds .description {
    font-size: 0.8em;
}

.blockconfigtable #rssfeeds tr.r0 {
  background-color: #ffffff;
}

.blockconfigtable #rssfeeds tr.r1 {
  background-color: #f0f0f0;
}
/***** /blocks/rss_client/styles.php end *****/

/***** /blocks/search_forums/styles.php start *****/

.block_search_forums .searchform {
    text-align: center;
}

.block_search_forums .searchform img {
    vertical-align: middle;
}

/***** /blocks/search_forums/styles.php end *****/

