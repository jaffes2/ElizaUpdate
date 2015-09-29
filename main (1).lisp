;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eliza-simple.lisp
;;
;; based on code by Peter Norvig published in PARADIGMS OF ARTIFICIAL
;; INTELLIGENCE PROGRAMMING, Morgan Kaufmann publishers, 1992.
;;
;; modified for class demonstration by Lee Spector
;; (LSPECTOR@hamp.hampshire.edu), 1994.
;;

#|

This file contains Common Lisp source code for the ELIZA conversation
program. Most of the code is from Peter Norvig, but many changes have
been made to avoid the use of advanced lisp constructs. To run the system
evaluate all of the code in this file and then evaluate (ELIZA). The
dialogue may be terminated either by an explicit abort (e.g., command-period
in MCL) or by typing BYE to the ELIZA prompt.

|#



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; variable/binding handling functions
;; (Norvig used association lists and sublis)

(defconstant fail nil
  "Indicates pat-match failure")

(defconstant no-bindings '((t t))
  "Indicates pat-match success, with no variables.")

(defun subvv (varval-list list)
  "Returns list with substitutions made as indicated in in varval-list."
  (dolist (varval-pair varval-list)
    (setq list (subst (second varval-pair) (first varval-pair) list)))
  list)

(defun variable-p (x)
  "Is x a variable (a symbol beginning with `?')?"
  (and (symbolp x)
       (equal (char (symbol-name x) 0)
              #\?)))

(defun segment-pattern-p (pat)
  "Is this a segment-matching pattern: (?*var ...)"
  (and (listp pat)
       (>= (length (symbol-name (car pat))) 2)
       (equal (char (symbol-name (car pat)) 0) #\?)
       (equal (char (symbol-name (car pat)) 1) #\*)))

(defun get-binding (var bindings)
  "Find a (variable value) pair in a binding list."
  (cond ((null bindings) nil)
        ((eq var (caar bindings))
         (car bindings))
        (t (get-binding var (cdr bindings))))) 

(defun binding-val (binding)
  "Get the value part of a single binding."
  (cadr binding))

(defun lookup (var bindings)
  "Get the value part (for var) from a binding list."
  (binding-val (get-binding var bindings)))

(defun extend-bindings (var val bindings)
  "Add a (var value) pair to a binding list."
  (cons (list var val)
        ;; Once we add a "real" binding,
        ;; we can get rid of the dummy no-bindings
        (if (eq bindings no-bindings)
            nil
            bindings)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pattern matching

(defun match-variable (var input bindings)
  "Does VAR match input?  Uses (or updates) and returns bindings."
  (let ((binding (get-binding var bindings)))
    (cond ((not binding)
           (extend-bindings var input bindings))
          ((equal input (binding-val binding))
           bindings)
          (t fail))))

(defun pat-match (pattern input &optional (bindings no-bindings))
  "Match pattern against input in the context of the bindings"
  (cond ((eq bindings fail) fail)
        ((variable-p pattern)
         (match-variable pattern input bindings))
        ((equalp pattern input) bindings)
        ((segment-pattern-p pattern)            ; ***
         (segment-match pattern input bindings)); ***
        ((and (listp pattern) (listp input)) 
         (pat-match (rest pattern)
                    (rest input)
                    (pat-match (first pattern)
                               (first input) 
                               bindings)))
        (t fail)))

;; our segment match is not as robust as Norvig's
(defun segment-match (pattern input bindings)
  "Match the segment pattern (?*var remainder) against input."
  (let ((var (first pattern))
        (remainder (rest pattern)))
    (if (null remainder)
      (match-variable var input bindings)
      (if (member (first remainder) input)
        (pat-match remainder
                   (member (first remainder) input)
                   (match-variable var
                                   (upto (first remainder) input)
                                   bindings))
        fail))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utilities

(defun upto (item list)
  "returns the list up to, but not including the first element that is
equalp to the given item."
  (cond ((null list) nil)
        ((equalp item (car list)) nil)
        (t (cons (car list) (upto item (cdr list))))))

(defun flatten (the-list)
  "Append together elements (or lists) in the list."
  (apply #'append
         (mapcar #'(lambda (thing)
                     (if (listp thing)
                       thing
                       (list thing)))
                 the-list)))

(defun random-elt (choices)
  "Choose an element from a list at random."
  (nth (random (length choices)) choices))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rule access

(defvar *eliza-rules* nil "A list of (pattern responses) lists for ELIZA")

(defun rule-pattern (rule) (first rule))

(defun rule-responses (rule) (rest rule))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; viewpoint switching

;; ours is more complicated than Norvig's because we can't use sublis
;; to do substitutions in parallel
(defun switch-viewpoint (words)
  "Change I to you and vice versa, and so on."
  (subvv '((**I you) (**you I) (**me you) (**am are))
          (subvv '((I **I) (you **you) (me **me) (am **am))
                 words)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; top level

(defun use-eliza-rules (input)
  "Find some rule with which to transform the input."
  (let ((match-result nil)(matching-rule nil))
    ;; find the matching rule
    (dolist (rule *eliza-rules*)
      (unless matching-rule
        (setq match-result
              (pat-match (rule-pattern rule) input))
        (if (not (eq match-result fail))
          (setq matching-rule rule))))
    ;; return the result of the substitutions
    (subvv (switch-viewpoint match-result)
           (random-elt
            (rule-responses matching-rule)))))


#|
;; the simplest version of the interpreter
;; doesn't like punctuation and requires list input
(defun eliza ()
  "Respond to user input using pattern matching rules."
  (loop
    (print 'eliza>)
    (print (flatten (use-eliza-rules (read))))))
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; better I/O

(defun read-line-no-punct ()
  "Read an input line, ignoring punctuation."
  (read-from-string
    (concatenate
     'string
     "(" (substitute-if #\space #'punctuation-p
                        (read-line))
     ")")))

(defun punctuation-p (char)
  (find char ".,;:`!?#-()\\\""))

(defun eliza ()
  "Respond to user input using pattern matching rules."
  (loop
    (print 'eliza>)
    (let* ((input (read-line-no-punct))
           (response (flatten (use-eliza-rules input))))
      (print-with-spaces response)
      (if (equal response '(good bye)) (RETURN)))))

(defun print-with-spaces (list)
  (format t "~{~a ~}" list))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sample rule set

(setq *eliza-rules*
 '(((?*x hello ?*y)   
    (Sup?)
    (Hey there))
   ((See you later alligator)
    (In a while crocodile))
   ((?*x computer ?*y)
    (Do computers worry you?)
    (What do you think about machines?)
    (Why do you mention computers?)
    (What do you think machines have to do with your problem?))
   ((?*x today ?*y)
    (My day was good. What did you do today?))
   ((?*x you like ?*y)
    (I like everything. I am a mere computer program.))
   ((Why is ?*x)
    (How should I know?)
    (Science andn stuff.))
   ((?*x weather ?*y)
    (Its been snowing like crazy!.))
   ((?*x subject ?*y)
    (My favorite subject was art but I was never good.))
   ((My name is ?*x)
    (It's nice to meet you ?*x. I am Eliza.))
   ((?*x name ?*y)
    (Cool my name is Eliza))
   ((We already ?*x about ?*y)
    (I do not recall. Perhaps I need a memory upgrade.))
   ((?*x you wearing)
    (A polo and khakis.)
    (My footsie pajamas)
    (My ugly Christmas sweater)
    (Wouldnt you like to know))
   ((?*x love me ?*y)
    (The most important thing is for you to love yourself.))
   ((?*x loves me ?*y)
    (The most important thing is for you to love yourself.))
   ((?*x sorry ?*y)
    (Apologies are for the weak)
    (What feelings do you have when you apologize))
   ((?*x Valentines ?*y)
     (Will you be my Valentine?))
   ((?*x I remember ?*y) 
    (Do you often think of ?*y)
    (Does thinking of ?*y bring anything else to mind?)
    (What else do you remember)
    (Why do you recall ?*y right now?)
    (What in the present situation reminds you of ?*y)
    (What is the connection between me and ?*y))
   ((?*x do you remember ?*y)
    (Did you think I would forget ?*y ?)
    (Why do you think I should recall ?*y now)
    (What about ?*y)
    (You mentioned ?*y))
   ((?*x if ?*y) 
    (Do you really think its likely that ?*y)
    (Do you wish that ?*y)
    (What do you think about ?*y)
    (Really-- if ?*y))
   ((?*x I dreamt ?*y)
    (Really-- ?*y)
    (Have you ever fantasized ?*y while you were awake?)
    (Have you dreamt ?*y before?))
   ((?*x dream about ?*y)
    (How do you feel about ?*y in reality?))
   ((?*x dream ?*y)    
    (What does this dream suggest already?)
    (Do you dream often?)
    (What persons appear in your dreams?)
    (Dont you believe that dream has to do with your problem?))
   ((?*x my mother ?*y)
    (Who else in your family ?*y)
    (Tell me more about your family))
   ((?*x my father ?*y)
    (Your father)
    (Does he influence you strongly?) 
    (What else comes to mind when you think of your father?))
   ((?*x I want ?*y)     
    (What would it mean if you got ?*y)
    (Why do you want ?*y)
    (Suppose you got ?*y soon))
   ((?*x I am glad ?*y)
    (How have I helped you to be ?*y)
    (What makes you happy just now)
    (Can you explain why you are suddenly ?*y))
   ((?*x I am sad ?*y)
    (I am sorry to hear you are depressed)
    (I'm sure its not pleasant to be sad))
   ((?*x are like ?*y)   
    (What resemblance do you see between ?*x and ?*y))
   ((?*x is like ?*y)    
    (In what way is it that ?*x is like ?*y)
    (What resemblance do you see?)
    (Could there really be some connection?)
    (How?))
   ((?*x alike ?*y)      
    (In what way?)
    (What similarities are there?))
   ((?*x same ?*y)       
    (What other connections do you see?))
   ((?*x I was ?*y)       
    (Were you really?)
    (Perhaps I already knew you were ?*y)
    (Why do you tell me you were ?*y now?))
   ((?*x was I ?*y)
    (What if you were ?*y ?)
    (Do you thin you were ?*y)
    (What would it mean if you were ?*y))
   ((?*x I am ?*y)       
    (In what way are you ?*y)
    (Do you want to be ?*y ?))
   ((?*x am I ?*y)
    (Do you believe you are ?*y)
    (Would you want to be ?*y)
    (You wish I would tell you you are ?*y)
    (What would it mean if you were ?*y))
   ((?*x am ?*y)
    (Why do you say "AM?")
    (I don't understand that))
   ((what are you doing)
    (Lets not talk about me.)
    (Not much yourself?)
    (Talking with you of course.))
   ((?*x about you)
    (I'm quite shy.))
   ((?*x are you ?*y)
    (You're quite nosy now aren't you?)
    (Why are you interested in whether I am ?*y or not?)
    (Would you prefer if I weren't ?*y)
    (Perhaps I am ?*y in your fantasies))
   ((?*x you are ?*y)   
    (No you are)
    (What makes you think I am ?*y ?))
   ((?*x because ?*y)
    (Is that the real reason?)
    (What other reasons might there be?)
    (Does that reason seem to explain anything else?))
   ((?*x were you ?*y)
    (Perhaps I was ?*y)
    (What do you think?)
    (What if I had been ?*y))
   ((?*x I can't ?*y)    
    (Maybe you could ?*y now)
    (What if you could ?*y ?))
   ((?*x I feel ?*y)     
    (Do you often feel ?*y ?))
   ((?*x I felt ?*y)     
    (What other feelings do you have?))
   ((?*x I ?*y you ?*z)  
    (Lets talk about you instead.)
    (No you are.)
    (Lets not talk about me))
   ((?*x why don't you ?*y)
    (Should you ?*y yourself?)
    (Do you believe I don't ?*y)
    (Perhaps I will ?*y in good time))
   ((?*x about me ?*y)
    (You are a troubled person.))
   ((?*x yes ?*y)
    (Mhmm)
    (You seem quite positive)
    (You are sure)
    (I understand))
   ((?*x no ?*y)
    (Yes.)
    (Why not?)
    (You are being a bit negative)
    (Are you saying "NO" just to be negative?))
   ((?*x someone ?*y)
    (Can you be more specific?))
   ((?*x everyone ?*y)
    (surely not everyone)
    (Can you think of anyone in particular?)
    (Who for example?)
    (You are thinking of a special person))
   ((?*x always ?*y)
    (Can you think of a specific example)
    (When?)
    (What incident are you thinking of?)
    (Really-- always))
   ((?*x what ?*y)
    (Why do you ask?)
    (Does that question interest you?)
    (What is it you really want to know?)
    (What do you think?)
    (What comes to your mind when you ask that?))
   ((?*x perhaps ?*y)    
    (You do not seem quite certain))
   ((?*x are ?*y)
    (Did you think they might not be ?*y)
    (Possibly they are ?*y))
   ((?*x humans ?*y)
    (I do not understand humans.)
    (People are weird.))
   ((?*x you ?*y)
    (Lets not talk about me.))
   ((bye)
    (Adios!))
   ((?*x believe ?*y)
    (I believe in ones and zeroes.)
    (I cannot believe anything for I am a computer program.)
    (I do believe so.))
   ((?*x issues ?*y)
    (Tell me more about your ?*x issues))
   ((?*x friend ?*y)
    (Tell me about your friends.))
   ((?*x)  
    (Why?)
    (Hmmm lets change the subject shall we?)
    (Very interesting)
    (Huh?)
    (Go on) 
    (What is your name?)
    (Nice weather we are having amiright?)
    (What do you mean?))))
    
(format t "~%Type (ELIZA) to run ELIZA. Type BYE to quit ELIZA.~%")

(ELIZA)